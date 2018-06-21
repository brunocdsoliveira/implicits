module TypeCheck where

import Syntax

import Debug.Trace

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative

import qualified SystemF as F

checkTerm :: Term -> Either String (ContextType, F.Term)
checkTerm t 
 = runReaderT (evalStateT (typeCheck t) 0) E_Empty

-- TYPE CHECKER MONAD --------------------------------

type TC = StateT Int (ReaderT Env (Either String))

tcAbort :: TC a
tcAbort = lift (throwError "Abort!")

tcError :: String -> TC a
tcError msg = throwError msg

tcEnv :: TC Env
tcEnv = ask

tcFresh :: TC Var
tcFresh =
  do n <- get
     put (n + 1)
     return ("_fresh_" ++ show n)

-- ENVIRONMENT --------------------------------------

data Env
  = E_Empty
  | E_Var Var ContextType Env
  | E_TVar TVar Env
  | E_Imp ContextType Var Env

inEnv :: (Env -> Env) -> TC a -> TC a
inEnv = local 

tcLookupVar :: Var -> TC ContextType
tcLookupVar v = 
  do env <- tcEnv 
     go env
  where
    go E_Empty 
      = tcError ("Variable not found: " ++ v)
    go (E_Var w r env) 
      | w == v     = return r
      | otherwise  = go env
    go (E_TVar _ env)
      = go env
    go (E_Imp _ _ env)
      = go env

-- TYPE CHECKER --------------------------------------
elabCT :: ContextType -> F.Type
elabCT (CT_Univ tv ct)
  = F.Univ tv (elabCT ct)
elabCT (CT_Rule ct1 ct2)
  = F.Fun (elabCT ct1) (elabCT ct2)
elabCT (CT_Simp st)
  = elabST st

elabST :: SimpleType -> F.Type
elabST (ST_TVar tv)
  = F.TVar tv
elabST (ST_Fun ct1 ct2)
  = F.Fun (elabCT ct1) (elabCT ct2)
elabST (ST_Int)
  = F.IntTy
elabST (ST_Bool)
  = F.BoolTy

elabTSubst :: TSubst -> F.TSubst
elabTSubst = map (\(tv,st) -> (tv,elabST st))

-- TYPE CHECKER --------------------------------------

typeCheck :: Term -> TC (ContextType, F.Term)
typeCheck (TM_Var v)
 = (\ct -> (ct, F.Var v)) <$> tcLookupVar v
typeCheck (TM_Abs v ct1 t)
 = do (ct2, f) <- inEnv (E_Var v ct1) (typeCheck t)
      return (CT_Simp (ST_Fun ct1 ct2), F.Abs v (elabCT ct1) f) 
typeCheck (TM_App t1 t2)
 = do (ct1, f1) <- typeCheck t1
      case ct1 of
        CT_Simp (ST_Fun ct11 ct12) 
          -> do (ct2, f2) <- typeCheck t2
                if ct11 == ct2
                  then return (ct12, F.App f1 f2)
                  else tcError ("Function argument type mismatch, expected: " ++ show ct11 ++ ", found: " ++ show ct2)
        _ 
          -> tcError ("Expected function type, found: " ++ show ct1)
         
typeCheck (TM_TAbs tv t)
 = do (ct, f) <- inEnv (E_TVar tv) (typeCheck t)
      return (CT_Univ tv ct, F.TAbs tv f)
typeCheck (TM_TApp t st) 
 = do (ct, f) <- typeCheck t
      case ct of
        CT_Univ tv ct'
          ->
             return (substTVar tv st ct', F.TApp f (elabST st))
        _ 
          -> tcError ("Expected universal type, found: " ++ show ct)
         
typeCheck (TM_IAbs ct1 t)
 = do x <- tcFresh
      (ct2, f) <- inEnv (E_Imp ct1 x) (typeCheck t)
      return (CT_Rule ct1 ct2, F.Abs x (elabCT ct1) f)
typeCheck (TM_IApp t1 t2)
 = do (ct1, f1) <- typeCheck t1
      case ct1 of
        CT_Rule ct11 ct12
          ->
             do (ct2, f2) <- typeCheck t2
                if ct11 == ct2
                  then return (ct12, F.App f1 f2)
                  else tcError ("Implicit funtion argument type mismatch, expected: " ++ show ct11 ++ ", found: " ++ show ct2)
        _ 
          -> tcError ("Expected rule type, found: " ++ show ct1)
      
typeCheck (TM_Query ct)
 = do f <- resolve ct
      return (ct, f)
typeCheck (TM_Int n)
 = return (CT_Simp ST_Int, F.Int n)
typeCheck TM_True
 = return (CT_Simp ST_Bool, F.True)
typeCheck TM_False
 = return (CT_Simp ST_Bool, F.False)


resolve :: ContextType -> TC (F.Term)
resolve ct = res ct
  where

    res :: ContextType -> TC (F.Term)
    res (CT_Univ tv ct)
      = do f <- inEnv (E_TVar tv) (res ct)
           return (F.TAbs tv f)
    res (CT_Rule ct1 ct2)
      = do x <- tcFresh
           f <- inEnv (E_Imp ct1 x) (res ct2)
           return (F.Abs x (elabCT ct1) f)
    res (CT_Simp st)
      = do env <- tcEnv
           lkp env st

    lkp :: Env -> SimpleType -> TC (F.Term)
    lkp E_Empty st
      = tcError ("No matching rule found for: " ++ show st)
    lkp (E_Var _ _ env) st
      = lkp env st
    lkp (E_TVar _ env) st
      = lkp env st
    lkp (E_Imp ct x env) st
      = (    (do (f, cts) <- mtc ct (F.Var x) st [] []
                 return (do s <- traverse (traverse res) cts
                            return (F.substVars s f)
                        )
             ) 
         <|> 
             (do f <- lkp env st
                 return (return f))
        ) >>= \c -> c
        -- TODO: test for stability
 
    mtc :: ContextType -> F.Term -> SimpleType -> [(Var,ContextType)] -> [TVar] 
        -> TC (F.Term, [(Var,ContextType)])
    mtc (CT_Simp st') f st cts tvars
      = do s <- unify st' st tvars
           return (F.substTVarsInTerm (elabTSubst s) f, fmap (fmap (substTVars s)) cts)
    mtc (CT_Rule ct1 ct2) f st cts tvars
      = do x <- tcFresh
           mtc ct2 (F.App f (F.Var x)) st ((x,ct1):cts) tvars
    mtc (CT_Univ tv ct) f st cts tvars
      = mtc ct (F.TApp f (F.TVar tv)) st cts (tv:tvars)

unify :: SimpleType -> SimpleType -> [TVar] -> TC TSubst
unify st1 st2 tvars = 
     trace ("unify " ++ show st1 ++ " " ++ show st2 ++ " " ++ show tvars) $
     go1 st1 st2
  where
    go1 st1 st2
      | trace ("go1 " ++ show st1 ++ " " ++ show st2) $ False
      = error "UNREACHABLE"
    go1 (ST_TVar tv1) st2@(ST_TVar tv2)
      = if tv1 `elem` tvars
          then
            return [(tv1,st2)]
          else
            do guard (tv1 == tv2)
               return []
    go1 (ST_TVar tv1) st2@(ST_Fun ct1 ct2)
      = do guard (tv1 `elem` tvars)
           return [(tv1,st2)]
    go1 (ST_Fun ct1 ct2) (ST_TVar tv2)
      = empty
    go1 (ST_Fun ct11 ct12) (ST_Fun ct21 ct22)
      = do s1 <- go2 ct11 ct21
           s2 <- go2 (substTVars s1 ct12) (substTVars s1 ct22)
           return (s2 ++ s1)
    go1 ST_Int ST_Int
      = return []
    go1 (ST_TVar tv1) ST_Int
      | tv1 `elem` tvars
      = return [(tv1,ST_Int)]
    go1 ST_Bool ST_Bool
      = return []
    go1 (ST_TVar tv1) ST_Bool
      | tv1 `elem` tvars
      = return [(tv1,ST_Bool)]
    go1 _ _
      = empty

    go2 (CT_Univ tv1 ct1) (CT_Univ tv2 ct2)
      | tv1 == tv2
      = go2 ct1 ct2
    go2 (CT_Rule ct11 ct12) (CT_Rule ct21 ct22)
      = do go2 ct11 ct21
           go2 ct12 ct22
    go2 (CT_Simp st1) (CT_Simp st2)
      = go1 st1 st2
    go2 _ _
      = empty 

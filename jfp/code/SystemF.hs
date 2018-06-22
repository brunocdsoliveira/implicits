module SystemF where

import Text.PrettyPrint.HughesPJ

import Control.Monad.Except
import Control.Monad.Reader
import Control.Applicative

-- TYPES ----------------------

type TVar = String

data Type
  = Univ TVar Type
  | Fun Type Type
  | TVar TVar
  | IntTy
  | BoolTy
  deriving Eq

-- Substitution

substTVar :: TVar -> Type -> Type -> Type
substTVar tv t = go
  where
    go (Univ tv' t) 
      = Univ tv' (go t)
    go (Fun t1 t2)
      = Fun (go t1) (go t2)
    go t'@(TVar tv')
      | tv == tv'
      = t
      | otherwise
      = t'
    go IntTy
      = IntTy
    go BoolTy
      = BoolTy

type TSubst = [(TVar,Type)]

substTVars :: TSubst -> Type -> Type
substTVars s t
  = foldr (uncurry substTVar) t s


-- TERM -----------------------

type Var = String

data Term
 = Var Var
 | Abs Var Type Term
 | App Term Term
 | TAbs TVar Term
 | TApp Term Type
 | Int Integer
 | True
 | False

substVar :: Var -> Term -> Term -> Term
substVar v t = go
  where
    go (Var v')
     | v == v'
     = t
     | otherwise
     = Var v'
    go (Abs v' ty t')
     | v == v'
     = Abs v' ty t'
     | otherwise
     = Abs v' ty (go t') 
    go (App t1 t2)
     = App (go t1) (go t2)
    go (TAbs tv t')
     = TAbs tv (go t')
    go (TApp t' ty)
     = TApp (go t') ty
    go (Int n)
     = Int n
    go SystemF.True 
     = SystemF.True
    go SystemF.False
     = SystemF.False


type Subst = [(Var,Term)]

substVars :: Subst -> Term -> Term
substVars s t = foldr (uncurry substVar) t s

substTVarInTerm :: TVar -> Type -> Term -> Term
substTVarInTerm tv ty = go
  where
    go (Var v)
     = Var v
    go (Abs v ty' t)
     = Abs v (substTVar tv ty ty') (go t)
    go (App t1 t2)
     = App (go t1) (go t2)
    go (TAbs tv' t)
     | tv' == tv
     = (TAbs tv' t)
     | otherwise
     = TAbs tv' (go t)
    go (TApp t ty')
     = TApp (go t) (substTVar tv ty ty')
    go (Int n)
     = Int n
    go SystemF.True 
     = SystemF.True
    go SystemF.False
     = SystemF.False

substTVarsInTerm :: TSubst -> Term -> Term
substTVarsInTerm s t = foldr (uncurry substTVarInTerm) t s

-- PRETTY ------------------------

parens_ p q d = 
  if p > q then parens d else d

pretty :: Pretty a => a -> Doc
pretty x = pretty_ 0 x

class Pretty a where
  pretty_ :: Int -> a -> Doc

instance Pretty Type where
  pretty_ p (Univ tv t)
    = parens_ p 0 (text "forall" <+> text tv <> char '.' <+> pretty_ 0 t)
  pretty_ p (TVar tv)
    = text tv
  pretty_ p (Fun t1 t2)
    = parens_ p 2 (pretty_ 4 t1 <+> text "->" <+> pretty_ 2 t2)
  pretty_ p IntTy
    = text "int"
  pretty_ p BoolTy
    = text "bool"

instance Pretty Term where
  pretty_ p (Var v)
    = text v
  pretty_ p (Abs v ct t)
    = parens_ p 1 (char '\\' <> (text v <> char ':' <> pretty_ 0 ct) <> char '.' <> pretty_ 0 t)
  pretty_ p (App t1 t2)
    = parens_ p 1 (pretty_ 4 t1 <+> pretty_ 4 t2)
  pretty_ p (TAbs tv t)
    = parens_ p 1 (text "/\\" <> text tv <> char '.' <> pretty_ 0 t)
  pretty_ p (TApp t st) 
    = parens_ p 1 (pretty_ 4 t <> brackets (pretty_ 0 st))
  pretty_ p (Int n)
    = text (show n)
  pretty_ p SystemF.True
    = text "true"
  pretty_ p SystemF.False
    = text "false"

instance Show Type where
  show = render . pretty

instance Show Term where
  show = render . pretty

-- TYPE CHECKING --------------


checkTerm :: Term -> Either String Type
checkTerm t 
 = runReaderT (typeCheck t) E_Empty

-- TYPE CHECKER MONAD --------------------------------

type TC = ReaderT Env (Either String)

tcAbort :: TC a
tcAbort = lift (throwError "Abort!")

tcError :: String -> TC a
tcError msg = throwError msg

tcEnv :: TC Env
tcEnv = ask

-- ENVIRONMENT --------------------------------------

data Env
  = E_Empty
  | E_Var Var Type Env
  | E_TVar TVar Env

inEnv :: (Env -> Env) -> TC a -> TC a
inEnv = local 

tcLookupVar :: Var -> TC Type
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

-- TYPE CHECKER --------------------------------------

typeCheck :: Term -> TC Type
typeCheck (Var v)
 = tcLookupVar v
typeCheck (Abs v ty1 t)
 = do ty2 <- inEnv (E_Var v ty1) (typeCheck t)
      return (Fun ty1 ty2)
typeCheck (App t1 t2)
 = do ty1 <- typeCheck t1
      case ty1 of
        Fun ty11 ty12 
          -> do ty2 <- typeCheck t2
                if ty11 == ty2
                  then return ty12
                  else tcError ("Function argument type mismatch, expected: " ++ show ty11 ++ ", found: " ++ show ty2)
        _ 
          -> tcError ("Expected function type, found: " ++ show ty1)
typeCheck (TAbs tv t)
 = do ty <- inEnv (E_TVar tv) (typeCheck t)
      return (Univ tv ty)
typeCheck (TApp t ty2) 
 = do ty1 <- typeCheck t
      case ty1 of
        Univ tv ty1'
          ->
             return (substTVar tv ty2 ty1')
        _ 
          -> tcError ("Expected universal type, found: " ++ show ty1)
typeCheck (Int n)
 = return IntTy
typeCheck SystemF.True
 = return BoolTy
typeCheck SystemF.False 
 = return BoolTy

> {-# OPTIONS -XRankNTypes #-}

> module STLC where

> data PExp a = Lit Int | Var a | Lam Typ (a -> PExp a) | App (PExp a) (PExp a)

> newtype Exp = E {unE :: forall a. PExp a}

> data Typ = TInt | Fun Typ Typ deriving (Eq, Show)

> data PType = F Typ | P (Typ -> PType) -- no application case here

Needs unification for application, normally?

Can I merge the two functions?

> unknown :: PType
> unknown = P F
>
> tcheck :: Exp -> Typ -> Maybe Typ
> tcheck e t = check (unE e) (F t)
>
> infer :: Exp -> Maybe Typ
> infer e = check (unE e) unknown
>
> check :: PExp Typ -> PType -> Maybe Typ
> check (Lit x)       t | unify TInt  t   = return TInt
> check (Var t1)     t2 | unify t1    t2  = return t1
> check (App e1 e2)  t2                   = 
>   do  (Fun t1 t3) <- check e1 (P (\t -> abstract t t2))
>       check e2 (F t1)
>       return t3
> check (Lam t1 f)  t2                    = 
>    do  rt  <- returnTyp t1 t2
>        t   <- check (f t1) rt 
>        return (Fun t1 t)
> check _           _                     = Nothing

Concretize/Abstract issue:

The algorithm adds new "unification" variables in a structured format: 

- there is a one-to-one correspondence between adding a new unification variable and 
applications.

I think this one-to-one correspondence should be exploited.

Computes the partial return type

> returnTyp :: Typ -> PType -> Maybe PType
> returnTyp t1  (F (Fun t1' t2)) | t1 == t1'  = Just (F t2)
> returnTyp t1  (P f)                         = Just (concretize (f t1)) -- get rid of concretize ?
> returnTyp t1  _                             = Nothing

Unify expected type

> unify :: Typ -> PType -> Bool 
> unify t1 p = 
>   case inst t1 p of 
>     Just t2 -> t1 == t2
>     Nothing -> False
> 
> inst :: Typ -> PType -> Maybe Typ -- instantiate unknowns
> inst _            (F t) = Just t
> inst TInt         (P f) = 
>   case f TInt of
>      F TInt -> Just TInt
>      _      -> Nothing
> inst (Fun t1 t2)  (P f) = inst t2 (f t1)
  
concretize is partial!

> concretize :: PType -> PType
> concretize (F (Fun t1 t2)) = F t2
> concretize (P f)           = P (\t -> concretize (f t))

> abstract :: Typ -> PType -> PType
> abstract t1 (F t2) = F (Fun t1 t2)
> abstract t1 (P f)  = P (abstract t1 . f) 

> {-
> check (Lam t1 f) t2 n = -- is this right? unification happens here ?1 = t1, so one less guess!
>   case check (f t1) t2 (n-1) of 
>      Nothing -> error "Type error 5"
>      Just t -> Just (Fun t1 t)
> check _ _ _ = Nothing
> {-
> check (Lam t1 f) t2 n = 
>   case check (f t1) t2 n of 
>      Nothing -> error "Type error 5"
>      Just t -> if (n == 0) then 
>                   case t2 of 
>                      Fun t1' t' | t1' == t1 && t == t' -> Just (Fun t1 t)
>                      _ -> error "type error 5" 
>                else Just (Fun t1 t) -- there may still be an error?
> -}

Type-checking without lambda annotations

> -- check

Type-inference

> infer :: PExp Typ -> Int -> Maybe Typ
> infer (Lit x) 0 = Just TInt
> infer (Lit _) n = error "Integer found, but function expected"
> infer (Var t1) n | checkArity t1 n = Just t1
> infer (App e1 e2) n = 
>   case infer e1 (n+1) of
>      Nothing -> Nothing
>      Just t@(Fun t1 t2) -> 
>        case infer e2 0 of
>           Nothing -> Nothing
>           Just t3 | t1 == t3 -> Just t3
>           _       -> Nothing -- types do not match
>      _ -> error "Must be a function type"
> infer (Lam t1 f) n = -- is this right? Is the arity preserved?
>   case infer (f t1) n of
>      Nothing -> Nothing
>      Just t -> Just (Fun t1 t)
> infer _ _ = Nothing

> checkArity :: Typ -> Int -> Bool
> checkArity t          0 = True
> checkArity (Fun _ t)  n = checkArity t n


> buildType :: Int -> Typ -> String
> buildType 0 t = show t
> buildType n t = "t" ++ show n ++ " -> " ++ buildType (n-1) t
>
> msg :: (Int,Typ) -> Typ -> String
> msg (n,t1) t2 = "\nExpected: " ++ buildType n t1 ++ "\nInferred: " ++ show t2 

Returns the n-th return type

> strip :: Int -> Typ -> Maybe Typ
> strip 0 t            = Just t
> strip n (Fun t1 t2)  = strip (n-1) t2
> strip n _            = Nothing

> idTyp = Fun TInt TInt
> idExp = E (Lam TInt (\x -> Var x))

> appTyp = TInt
> appExp = E (App (unE idExp) (Lit 3))

> test1 = tcheck idExp idTyp
> test2 = tcheck idExp TInt
> test3 = tcheck appExp appTyp
> test4 = tcheck appExp idTyp

Older version

> {-
> tcheck :: PExp Typ -> Typ -> Bool
> tcheck (Lit x)      TInt                      = True
> tcheck (Var t1)     t2                        = t1 == t2
> tcheck (Lam t1 f)   (Fun t1' t2) | t1 == t1'  = tcheck (f t1) t2
> tcheck (App e1 e2)  t2                        = 
>   case tcheckFun e1 t2 of 
>      Nothing         -> False
>      Just (Fun t _)  -> tcheck e2 t  
> tcheck _            _                         = False
>
> tcheckFun :: PExp Typ -> Typ -> Maybe Typ
> tcheckFun e t = tcheckFun' e t 0
> 
> tcheckFun' :: PExp Typ -> Typ -> Int -> Maybe Typ
> tcheckFun' (Var t) t' n = 
>   case strip1 n t of
>      Nothing -> error "Type error when stripping"
>      Just t'' -> if (t' == t'') then Just t else error "Type error 2"
> tcheckFun' (App e1 e2) t2 n = 
>   case tcheckFun' e1 t2 (n+1) of
>      Nothing                           -> Nothing
>      Just t@(Fun t1 _) | tcheck e2 t1  -> Just t
>      _                                 -> error "type error 4" -- should not happen!
> tcheckFun' (Lam t1 f) t2 0 | tcheck (f t1) t2 = Just (Fun t1 t2)
> tcheckFun' (Lam t1 f) t2 n = 
>   case tcheckFun' (f t1) t2 (n-1) of 
>      Nothing -> error "Type error 5"
>      Just t -> Just (Fun t1 t)
> tcheckFun' _ _ _ = Nothing  

| strip n t == t' = Just t

Returns the n-th return type of a function type

> strip1 :: Int -> Typ -> Maybe Typ
> strip1 0 (Fun t1 t2)  = Just t2
> strip1 n (Fun t1 t2)  = strip1 (n-1) t2
> strip1 n _            = Nothing
> -}

undefined -- tcheck e1 (Fun t1 t2)

> -}
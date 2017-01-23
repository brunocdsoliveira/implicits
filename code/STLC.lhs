> {-# OPTIONS -XRankNTypes #-}

> module STLC where

> data PExp a = Lit Int | Var a | Lam Typ (a -> PExp a) | App (PExp a) (PExp a)

> newtype Exp = E {unE :: forall a. PExp a}

> data Typ = TInt | Fun Typ Typ deriving (Eq, Show)

Needs unification for application, normally?

Can I merge the two functions?

> tcheck :: Exp -> Typ -> Maybe Typ
> tcheck e t = check (unE e) t 0 
>
> check :: PExp Typ -> Typ -> Int -> Maybe Typ
> check (Lit x) TInt 0 = Just TInt
> check (Lit _) TInt n = error "Integer found, but function returning Int expected"
> check (Var t1) t2 n = 
>   case strip n t1 of
>      Nothing -> error (msg (n,t2) t1)
>      Just t3 -> if (t3 == t2) then Just t1 else error (msg (n,t2) t1)
> check (App e1 e2) t2 n = 
>   case check e1 t2 (n+1) of
>      Nothing            -> Nothing
>      Just t@(Fun t1 t3) {-| t2 == t3-} -> -- is this check redundant? t3 a better type?  need to strip?
>         case check e2 t1 0 of 
>            Nothing -> Nothing
>            Just _ -> Just t3 
>      _                                 -> error "type error 4" -- should not happen!
> check (Lam t1 f) t@(Fun t1' t2) 0 | t1 == t1' = 
>   case check (f t1) t2 0 of
>      Nothing -> Nothing
>      Just _ -> Just t  
> check (Lam t1 f) t 0  = error ("\nExpected: " ++ show t ++ "\nInferred: " ++ show t1 ++ " -> ?") 
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
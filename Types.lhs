> {-# OPTIONS -XRankNTypes #-}

> module Types where

> data PType a = 
>     Var a 
>   | Fun (PContext a) (PContext a)
> 
> data PContext a = 
>     Type (PType a) 
>   | Forall (a -> PContext a) 
>   | Rule (PContext a)  (PContext a)

> instance Eq (PType a) where

> instance Eq (PContext a) where

> newtype Type = T {unT :: forall a . PType a}
>
> newtype Context = C {unC :: forall a . PContext a}

System F (move to another file):

-- > data FExp v t = FVar v | FTVar t | Lam (v -> FExp v t) | Abs (t -> FExp v t) | App (

Resolution type checking

> tcResolve :: [PContext Int] -> PContext Int -> Int -> Bool
> tcResolve env (Forall f) n    = tcResolve env (f n) (n+1)
> tcResolve env (Rule p1 p2) n  = tcResolve (p1:env) p2 n 
> tcResolve env (Type t) n      = 
>   case typLookup env t of
>      Nothing -> False
>      Just x -> typResolve env x t n
>
> typResolve :: [PContext Int] -> PContext Int -> PType Int -> Int -> Bool
> typResolve env (Type t1) t2 n   = True -- t1 == t2?
> typResolve env (Rule p1 p2) t n = tcResolve env p1 n && typResolve env p2 t n
> typResolve env (Forall f) t n   = undefined -- unification ?  
>
> typLookup :: [PContext Int] -> PType Int -> Maybe (PContext Int)
> typLookup []      t  = Nothing
> typLookup (p:ps)  t  = if entails p t then Just p else typLookup ps t
>
> entails :: PContext Int -> PType Int -> Bool
> entails (Type t1) t2 = t1 == t2 -- type equality
> entails (Forall f) t = undefined
> entails (Rule p1 p2) t = entails p2 t
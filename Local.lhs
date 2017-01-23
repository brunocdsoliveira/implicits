> {-# OPTIONS -fglasgow-exts #-}

> module Local where

> newtype EqD a = EqD {eq :: a -> a -> Bool}

> f :: ( ?eqD :: EqD a) => a -> a -> Bool
> f = undefined 

> newtype Id a = Id a

> instance (?eqD :: EqD a) => Eq (Id a) where
>   (Id x) == (Id y) = eq ?eqD x y

> v1 = Id 3 
> v2 = Id 4

> myEq1 :: EqD Int
> myEq1 = EqD {eq = \x y -> x == y}

> myEq2 :: EqD Int
> myEq2 = EqD {eq = \_ _ -> True}

> myEq3 :: Eq a => EqD a
> myEq3 = EqD {eq = \x y -> x == y}

> -- myEqList :: Eq a => EqD [a]
> -- myEqList

> p = (let ?eqD = myEq1 in v1 == v2, let ?eqD = myEq2 in v1 == v2)

An apparently equivalent program that misbehaves

> q = let ?eqD = myEq1 in (v1 == v2, let ?eqD = myEq2 in v1 == v2)

> u = let ?eqD = myEq3 in (v1 == v2, let ?eqD = myEq2 in v1 == v2)

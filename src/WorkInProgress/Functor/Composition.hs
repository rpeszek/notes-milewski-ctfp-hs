-- TODO this is temporary will needs to move to lhs

-- P1 CH7 Functors
-- P1 CH8 Functoriality (Identity)

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances, TypeFamilies,
               DataKinds #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}
-- TypeSynonymInstances

module WorkInProgress.Functor.Composition where

-- import qualified Control.Category as Cat


newtype FCompose f g a = FCompose { getFComp :: f (g a) }
instance (Functor f, Functor g) => Functor (FCompose f g) where
    fmap f (FCompose x) = FCompose (fmap (fmap f) x)

-- infixr 0 :.
type f :. g = FCompose f g

{-
   (f :. g) :. h a ==
   FCompose (f :. g (h a)) ==
   FCompose (FCompose f (g (h x)))

   f :. (g :. h) x ==
   FCompose (f ((g :. h) x)) ==
   FCompose (f (FCompose (g (h x))))
-}

iso1 :: Functor f => ((f :. g) :. h) a -> (f :. (g :. h)) a
iso1 (FCompose (FCompose fgh_x)) = FCompose (fmap FCompose fgh_x)

iso2 :: Functor f => (f :. (g :. h)) a -> ((f :. g) :. h) a
iso2 (FCompose f_comp_ghx) =  FCompose (FCompose $ fmap getFComp f_comp_ghx)

-- iso1 x = x

newtype Identity a = Identity a
instance Functor Identity where
    fmap f (Identity x) = Identity (f x)

-- newtype Identity a = Identity { getIdentity :: a }
-- instance Functor Identity where
--     fmap f m = Identity (f (getIdentity m))


{-|
  Functors are morphisms between categories (Category Cat).
  In Haskell functors are morphisms acting on a single object category.
  (Hask being the only object.)

  Cheat-sheet
  class Category cat where
     id :: cat a a
     (.) :: cat b c -> cat a b -> cat a c

  Unfortunately we cannot do something like this:
     instance Category Functor where
        id = Indentity
        (.) = :.
 -}

{-|
  CatMorphism (* -> *) -> * -> * -> Constraint
 -}
--  THESE WORK!
-- class Functor f => CatMorphism f a b where
-- instance Functor f => CatMorphism f a (f a)
--
-- instance (CatMorphism Identity a a)
-- instance (CatMorphism f b c, CatMorphism g a b) => CatMorphism (FCompose f g) a c

-- Kind Category
class KCategory cat where
   type KId cat :: * -> *
   type KComp cat :: (* -> *) -> (* -> *) -> * -> *

data CatInHaskell = CatInHaskell

instance KCategory CatInHaskell where
   type KId CatInHaskell = Identity
   type KComp CatInHaskell =  FCompose



{-
 Cheat-sheet
 class Category hom where
     id :: hom a a
     (.) :: hom b c -> hom a b -> hom a c
-}

-- newtype FComposeAsCat f g = FComposeAsCat { getFCompP :: forall x. FCompose f g x}
-- instance Cat.Category FunctorAsMorphism where
--  id = undefined
  -- (.) = undefined
--  (FComposeAsCat bc) . (FComposeAsCat ab) = FComposeAsCat $ FCompose (getFComp bc . getFComp ab)

{-
this polykinds does not do it
we need type equality constraints

> class K2Category cat where
>    type K2Id cat :: k -> k
>    type K2Comp cat :: (k2 -> k3) -> (k1 -> k2) -> k1 -> k1

> instance K2Category OurCategory where
>    type K2Id OurCategory = Identity
>    type K2Comp OurCategory = FCompose

-}
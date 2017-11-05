-- TODO this is temporary will needs to move to lhs

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module WorkInProgress.NaturalTransformation where

import qualified Control.Category as Cat
import WorkInProgress.Functor.Composition ((:.))
import qualified WorkInProgress.Functor.Composition as FComp

infixr 0 :~>
{-|
    Type synonym for natural transformation (NT) from @f@ to @g@.
    Typically just ~> is used (Purescript, Scalaz)
    I keep with convention of type level operators starting with :
 -}
type f :~> g = forall x. f x -> g x


{-|
    vertical composition of NT-ies reduces to (.)
 -}
verticalComp :: g :~> h -> f :~> g -> f :~> h
verticalComp gh fg = gh . fg

{-|
    Naturality condition.

    Commuting diagram of how f :: a -> b is mapped under 2 functors.
    This means (assuming both are Functors) naturality1 '==' naturality2

    The actual formula should be:
       fmap_G f . alpha_a = alpha_b . fmap_F f

    but compiler figures out which functor to use and polymorphism of alpha allows
    to drop types _a and _b from the formula
 -}
naturality1 :: Functor g => f :~> g -> (a -> b) -> f a -> g b
naturality1 alpha f = fmap f . alpha

naturality2 :: Functor f => f :~> g -> (a -> b) -> f a -> g b
naturality2 alpha f = alpha . fmap f

{-
 Cheat-sheet
 class Category cat where
     id :: cat a a
     (.) :: cat b c -> cat a b -> cat a c
-}
{-|
    Wrapped :~> that implements Functor Category with NTs as morphisms
 -}
newtype NTVert f g = NTVert { ntVert :: f :~> g }

instance Cat.Category (NTVert) where
    id = NTVert id
    NTVert f . NTVert g = NTVert (f `verticalComp` g)

{-|
    Horizontal composition of NT-ies is NT between composed functors
    α :: F -> F'
    β :: G -> G'
    β ∘ α :: G ∘ F -> G'∘ F'

    Note all of these should be Functors but for the implementation we just need one.
    Again, commuting diagrams say that horizontalComp1 '==' horizontalComp2

    In general we would have something like
        G'α_a ∘ β_F a  == β_F'a ∘ G α_a

    but parametricity/polymorphism arguments allow us to write simple code.

    (.) represents Hask morphism
    Note a much simpler implementation
    fmap (beta . fmap alpha)
    with this error
     Expected type: (:.:) b1 a1 x -> (:.:) b2 a2 x
        Actual type: FComp.FCompose b2 a2 (b1 (a1 x0))
                     -> FComp.FCompose b2 a2 (b2 (a2 x0))
    this is because fmap acts on x in FCompose a b x leaving a and b unchanged
 -}
horizontalComp1 :: Functor g =>
                    g :~> g' -> f :~> f' -> g :. f :~> g' :. f'
horizontalComp1 beta alpha =
   (\(FComp.FCompose x) -> FComp.FCompose $ beta . fmap alpha $ x)

horizontalComp2 :: Functor g' =>
                    g :~> g' -> f :~> f' -> g :. f :~> g' :. f'
horizontalComp2 beta alpha =
   (\(FComp.FCompose x) -> FComp.FCompose $ fmap alpha . beta $ x)


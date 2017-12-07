{-# LANGUAGE TypeOperators, Rank2Types #-}

{-
Trivial exercises/theorems about natural transformations
-}

module Trivialities.NTProps where

import Data.Either
import qualified GHC.Base as B (id)
import CTNotes.P1Ch10_NaturalTransformations
import CTNotes.P1Ch08a_BiFunctorAsFunctor


ntsArePolyFunctions :: f :~> g -> f x -> g x
ntsArePolyFunctions = B.id

-- | this does not compile, nor does it make sense since x would be considered fixed (not polymorphic)
-- | however, I can use any poly function as f :~> g
-- polyFunctionsAreNts :: (f x -> g x) -> f :~> g
-- polyFunctionsAreNts f = f

-- from the book
-- https://bartoszmilewski.com/2015/02/03/functoriality/

newtype BiComp bf fu gu a b = BiComp (bf (fu a) (gu b))

instance (Bifunctor bf, Functor fu, Functor gu) =>
  Bifunctor (BiComp bf fu gu) where
    bimap f1 f2 (BiComp x) = BiComp ((bimap (fmap f1) (fmap f2)) x)

type Comp2 bf fu gu a = BiComp bf fu gu a a

{- 
Two sided isos, one is shown
-}

-- | (a * b) ^ c == a ^ c *  b ^ c
pairTh ::  f :~> g -> f :~> h -> f :~> Comp2 (,) g h
pairTh fg fh = \fx -> BiComp (fg fx, fh fx)

-- | a ^ (b + c) == a ^ b *  a ^ b
-- | GHC will not compile this
-- either :: (Comp2 Either g h) :~> f -> (g :~> f, h :~> f)
-- either ghf = undefined -- (\gx -> ghf (BiComp $ Left gx), \hx -> ghf (BiComp $ Right hx))
-- | but this works
eitherTh :: ((Comp2 Either g h) x ->  f x) -> (g x -> f x, h x -> f x)
eitherTh ghf = (\gx -> ghf (BiComp $ Left gx), \hx -> ghf (BiComp $ Right hx))



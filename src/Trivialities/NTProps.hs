{-# LANGUAGE TypeOperators, Rank2Types #-}

{-
Trivial exercises/theorems about natural transformations
-}

module Trivialities.NTProps where

import Data.Either
import qualified GHC.Base as B (id)
import CTNotes.P1Ch10_NaturalTransformations
import CTNotes.P1Ch08a_BiFunctorAsFunctor
import CTNotes.P1Ch08b_BiFunctorComposition (Comp2(..))


ntsArePolyFunctions :: f :~> g -> f x -> g x
ntsArePolyFunctions = B.id

-- | this does not compile, nor does it make sense since x would be considered fixed (not polymorphic)
-- | however, I can use any poly function as f :~> g
-- polyFunctionsAreNts :: (f x -> g x) -> f :~> g
-- polyFunctionsAreNts f = f

{- 
Two sided isos, one is shown
-}

-- | (a * b) ^ c == a ^ c *  b ^ c
pairTh ::  f :~> g -> f :~> h -> f :~> Comp2 (,) g h
pairTh fg fh = \fx -> Comp2 (fg fx, fh fx)

-- | a ^ (b + c) == a ^ b *  a ^ b
-- | GHC will not compile this
-- either :: (Comp2 Either g h) :~> f -> (g :~> f, h :~> f)
-- either ghf = undefined -- (\gx -> ghf (BiComp $ Left gx), \hx -> ghf (BiComp $ Right hx))
-- | but this works
eitherTh :: ((Comp2 Either g h) x ->  f x) -> (g x -> f x, h x -> f x)
eitherTh ghf = (\gx -> ghf (Comp2 $ Left gx), \hx -> ghf (Comp2 $ Right hx))



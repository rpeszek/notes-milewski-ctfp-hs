|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch03a_NatsCat

Work in progress

Shows how to represent Monoid-like category (Natural numbers with +0 (id), +1, +2 morphisms) using Haskell.

> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE PolyKinds #-}
>
> module CTNotes.P1Ch03a_NatsCat where 
> import GHC.TypeLits
> import Data.Proxy
  
  
> data NatMorph (a :: Nat) (b :: Nat) = NatMorph { morph :: Integer -> Integer }
  
> defNatPlusMorph :: KnownNat m => Proxy m -> NatMorph n (n + m)
> defNatPlusMorph proxy = NatMorph ( (+) (natVal proxy))
  
> add0 = defNatPlusMorph (Proxy :: Proxy 0)
  
> add2 = defNatPlusMorph (Proxy :: Proxy 2)

  -- :t add2 
  -- add2 :: NatMorph n (n + 2)

> add2Test = morph add2
  
add2Test 3 prints 5
  
> compNatMorph :: NatMorph b c -> NatMorph a b -> NatMorph a c
> compNatMorph m1 m2 = NatMorph (morph m1 . morph m2)
  
> add4 = add2 `compNatMorph` add2
> add4Test = morph add4
  
add4Test 3 prints 7
  
Using Control.Category compiles but it should not! Some GHC issues where the errors show up on usage not instance
  -- instance C.Category NatMorph where
  --  id = add0
  --  (.) = compNatMorph
  
> class CategoryK (cat :: k -> k -> *)  where
>       cid :: cat a a
>       ccomp :: cat b c -> cat a b -> cat a c
  
> instance CategoryK NatMorph where
>    cid = add0
>    ccomp = compNatMorph
  
  
  
> add4' =  add2 `ccomp` add2 

:t add4`
add4' :: NatMorph a ((a + 2) + 2)

Even TODOs are TODO
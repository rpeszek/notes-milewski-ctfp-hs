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
> import Control.Category 
> import qualified GHC.Base as B (id,(.))
> import Prelude(Integer, (+), ($), (*))
 
> data NatCatType = NatPlus | NatMultiply
  
> data NatMorph (t:: NatCatType) (a :: Nat) (b :: Nat) = NatMorph { morph :: Integer -> Integer }
  
> defNatPlusMorph :: KnownNat m => Proxy m -> NatMorph 'NatPlus n (n + m)
> defNatPlusMorph proxy = NatMorph ( (+) (natVal proxy))
  
> add0 = defNatPlusMorph (Proxy :: Proxy 0)
  
> add2 = defNatPlusMorph (Proxy :: Proxy 2)

  -- :t add2 
  -- add2 :: NatMorph n (n + 2)

> add2Test = morph add2
  
add2Test 3 prints 5
  
> compNatMorph :: NatMorph t b c -> NatMorph t a b -> NatMorph t a c
> compNatMorph m1 m2 = NatMorph (morph m1 B.. morph m2)
  
> add4 = add2 `compNatMorph` add2
> add4Test = morph add4
  
add4Test 3 prints 7

  
```
class Category cat where
       id :: cat a a
       (.) :: cat b c -> cat a b -> cat a c
  
instance Category (->) where ...  
```
`PolyKinds` pragma causes `Category` to infer most general type on `cat` which is `k -> k -> *`
so `Category` class automatically infers scope to `Nat -> Nat -> *`
  
> instance Category (NatMorph 'NatPlus) where
>    id = add0
>    (.) = compNatMorph
  
> add4' =  add2 . add2 

:t add4`
add4' :: NatMorph a ((a + 2) + 2)


> defMultiplyMorph :: KnownNat m => Proxy m -> NatMorph 'NatMultiply n (n * m)
> defMultiplyMorph proxy = NatMorph ( (*) (natVal proxy))

> mul1 = defMultiplyMorph (Proxy :: Proxy 1)

> instance Category (NatMorph 'NatMultiply) where
>     id = mul1
>     (.) = compNatMorph

mult4' = defMultiplyMorph (Proxy :: Proxy 2) . defMultiplyMorph (Proxy :: Proxy 2)


Even TODOs are TODO
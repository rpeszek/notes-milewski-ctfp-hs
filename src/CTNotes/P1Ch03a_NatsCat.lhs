|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch03a_NatsCat

Notes about CTFP Part 1 Chapter 3. Examples of categories.  Natural numbers.
============================================================================
This note shows how represent the following natural number based categories in Haskell: 
``` 
  Objects: 0 (initial), 1, 2, 3, ...  
  Morphisms: (+0) (id), (+1), (+2), (+3), ... 
``` 
and  
```
  Objects: 0 (terminal), 1 (initial), 2, 3, ...  
  Morphisms: (*0), (*1) (id), (*2), (*3), ... 
``` 

Interestingly, these categories can be implemented as instances of `Control.Category` `Category` class.
This was not know to me until very recently.  `Category` class is kind polymorphic and works with 
kinds other than `*`.  This note uses dependent types-like features available in Haskell.

[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 3](https://bartoszmilewski.com/2014/12/05/categories-great-and-small/) defines
monoid as a single object category so this note is a bit different.

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

In this construction Objects are types of kind `Nat` and morphism have type `NatMorph`.
`DataKinds` pragma allows me to easily define type level enumerations
as well as to restrict morphism to the kind I want.
 
> data NatCatType = NatPlus | NatMultiply
> data NatMorph (t:: NatCatType) (a :: Nat) (b :: Nat) = NatMorph { morph :: Integer -> Integer }

`NatPlus` category
------------------
  
> defNatPlusMorph :: KnownNat m => Proxy m -> NatMorph 'NatPlus n (n + m)
> defNatPlusMorph proxy = NatMorph ( (+) (natVal proxy))
>  
> add0 = defNatPlusMorph (Proxy :: Proxy 0)
> add2 = defNatPlusMorph (Proxy :: Proxy 2)
> add2Test = morph add2

here is the ghci output:
```bash
λ> :t add2 
add2 :: NatMorph 'NatPlus n (n + 2)

λ> add2Test 3
5
```
(prettified the GHC output, GHC tends to use `GHC.TypeLits.+ 2` instead of `2`)

Composition is polymorphic (will work for both `NatPlus` and `NatMultiply` case):
  
> compNatMorph :: NatMorph t b c -> NatMorph t a b -> NatMorph t a c
> compNatMorph m1 m2 = NatMorph (morph m1 B.. morph m2)
>  
> add4 = add2 `compNatMorph` add2
> add4Test = morph add4

ghci output shows that GHC infers types nicely:
```bash 
λ> :t add4
add4 :: NatMorph 'NatPlus a ((a + 2) + 2)
 
λ> add4Test 3
7
```

Here is the definition of `Category` quoted from base package `Control.Category` module: 
```
class Category cat where
       id :: cat a a
       (.) :: cat b c -> cat a b -> cat a c
  
instance Category (->) where ...  
```

`PolyKinds` pragma causes `Category` to infer most general type on `cat` which is `k -> k -> *`
so `Category` class automatically infers `Nat -> Nat -> *` for me      
(Note `NatMorph` has kind `NatMorph :: NatCatType -> Nat -> Nat -> *`):
  
> instance Category (NatMorph 'NatPlus) where
>    id = add0
>    (.) = compNatMorph

Here is example of polymorphic use of `(.)`:
  
> add4' =  add2 . add2 

ghci output:
```bash
λ> :t add4`
add4' :: NatMorph 'NatPlus a ((a + 2) + 2)

λ> morph add4` $ 3
7
```

_Small note:_ this does not compile, GHC does not allow me to supply theorems
```
add4'' :: NatMorph 'NatPlus a (a + 4)
add4'' =  add2 . add2 
```

`NatMultiply` case
------------------

> defMultiplyMorph :: KnownNat m => Proxy m -> NatMorph 'NatMultiply n (n * m)
> defMultiplyMorph proxy = NatMorph ( (*) (natVal proxy))
>
> mul1 = defMultiplyMorph (Proxy :: Proxy 1)
>
> instance Category (NatMorph 'NatMultiply) where
>     id = mul1
>     (.) = compNatMorph
>
> mult4' = defMultiplyMorph (Proxy :: Proxy 2) . defMultiplyMorph (Proxy :: Proxy 2)

ghci output:
```bash
λ> morph mult4' $ 2
8
```

TODO:  Many CT goodies are very general.  Special casing 
everything to Hask seems like missing out on generality that is already there.
Learning more about non Hask categories and how different cats play with Hask 
seems important and potentially useful.  

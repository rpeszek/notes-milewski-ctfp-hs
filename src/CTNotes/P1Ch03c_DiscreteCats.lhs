|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch03c_DiscreteCat

Note about CTFP Part 1 Chapter 3. Categories great and small.  Discrete categories in Haskell
=============================================================================================

I am searching for (other than Hask) examples of categories in Haskell. This note is about discrete categories.

Ref: https://hackage.haskell.org/package/categories-1.0.7/docs/src/Control-Category-Discrete.html  
Ref: https://hackage.haskell.org/package/category-extras-0.53.5/docs/Control-Category-Discrete.html  

This note supplements [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 3. Categories great and small](https://bartoszmilewski.com/2014/12/05/categories-great-and-small/)

> {-# LANGUAGE DataKinds
>  , KindSignatures
>  , TypeOperators
>  , FlexibleInstances 
>  , PolyKinds 
>  , ScopedTypeVariables
> #-}
>
> module CTNotes.P1Ch03c_DiscreteCats where
> import Data.Proxy
> import Data.Type.Equality
> import GHC.TypeLits


Discrete Categories
-------------------
Discrete Categories have only id morphisms.  `category-extras` has defined GADT `Discrete` as

```
data Discrete a b where 
	Refl :: Discrete a a

instance Category Discrete where
	id = Refl
	Refl . Refl = Refl
```
 
__Type Equality__  
Data.Type.Equality (base package) defines propositional equality (:~:) for types.

The documentation for Data.Type.Equality says that `a :~: b` is inhabited by a proof that `a` and `b` are 
the same type. That sounds extremely sophisticated as if ghc had some secret knowledge.
It does not, GADT `a :~: b` has only one constructor 
(notice that `Discrete` and `:~:` are equivalent)
```
data a :~: b where  
  Refl :: a :~: a
```
and ghc will not let you construct `a :~: b` unless you use the same type.  

For example, I can check how much ghc knows about type level natural numbers:

> proof2eq1p1 ::  2 :~: (1 + 1)
> proof2eq1p1 = Refl

or

> proofAdd' :: forall (n :: Nat) . (n + 2) :~: (n + (1 + 1))
> proofAdd' = Refl

but this will not compile:

```
proofAdd'' :: forall (n :: Nat) . (n + 2) :~: ((n + 1) + 1)
proofAdd'' = Refl

ghc output:
  • Couldn't match type ‘n + 2’ with ‘(n + 1) + 1’
      Expected type: (n + 2) :~: ((n + 1) + 1)
        Actual type: (n + 2) :~: (n + 2)
      NB: ‘+’ is a type function, and may not be injective
   ...
```

`:~:` has instance of Category from Control.Category which is identical to the above
instance of `Discrete`.  (See my `IdrisTddNotes` for some fun proofs about `Nat` type)



__Coercion__  
In my search for non-Hask categories I also found `Data.Type.Coercion`.
It is not exactly discrete, rather it describes an equivalence relation 
(reflexive, symmetric, and transitive relation) on types.  Coercion can be viewed as 
representational equality.  It basically says that 2 types have the same representation
in memory.  
`Coercion` has instance of Category from Control.Category as well.

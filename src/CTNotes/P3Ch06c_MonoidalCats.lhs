|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch06c_MonoidalCats

Notes on Monoidal Categories in Haskell.  Mostly because I will need them later. 
__Very much work-in-progress__  

Refs:: `category-extras`, `categories` packages

> {-#LANGUAGE MultiParamTypeClasses, FunctionalDependencies#-}
> module CTNotes.P3Ch06c_MonoidalCats where
> import CTNotes.P1Ch08c_BiFunctorNonHask
> import Data.Void

`category-extras`, `categories` define Monoidal in terms of more general type classes: Associative Bifunctor, HasIdentity
This bundles the concept into one and uses less generic approach.  
`i` plays the role of identity object, `bi` is the tensor product.

> class CBifunctor bi cat cat => Monoidal cat bi i | cat bi -> i where
>   associator :: cat (bi (bi a b) c) (bi a (bi b c))
>   lunitor :: cat (bi i a) a
>   runitor :: cat (bi a i) a

These correspond to
```
α_{a b c} :: (a ⊗ b) ⊗ c -> a ⊗ (b ⊗ c)
λ_a :: i ⊗ a -> a
ρ_a :: a ⊗ i -> a
```

Coherence conditions:
```
TODO
```

in Haskell:

```
TODO
```

Instances
---------
Famously (in pseudo-Haskell)  
```
instance Monoidal Endo Composition Identity
``` 
([N_P1Ch07_Functors_Composition](N_P1Ch07_Functors_Composition))
where `Endo` is category of Endofunctors on Hask, `Composition` is functor composition, and `Identity` is identity functor.

> instance Monoidal (->) (,) Void where
>      associator = undefined
>      lunitor = snd
>      runitor = fst

(Enriched Category P3 Ch12 notes will have more instances).


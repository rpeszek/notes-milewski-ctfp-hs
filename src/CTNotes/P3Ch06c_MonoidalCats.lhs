|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch06c_MonoidalCats

Greg Pfeil gave a great presentation at Boulder Haskell Meetup about monoids, 
monoidal categories expressed in Haskell, including
expressing Monad as a Functor Monoid:

https://github.com/sellout/category-parametric-talk/tree/master/monoiad  
https://github.com/sellout/category-parametric-talk/blob/master/monoiad/haskell.org  
https://github.com/sellout/category-parametric-talk/blob/c97d89f7dc4ebb4158682435adc1baaf3ff88142/monoiad/haskell.org

I will not do a better job here. This note has been superseded by Greg's work. 

__My notes from before Greg's talk:__  
Notes on monoidal categories in Haskell.  Mostly because I will need them later. 

Refs:: `category-extras`, `categories` packages

> {-# LANGUAGE MultiParamTypeClasses
>  , FunctionalDependencies
>  , PolyKinds
>  , TypeFamilies
>  , TypeOperators
>  , TypeInType 
>  , AllowAmbiguousTypes -- needed for NonHaskMonoidal nhassociator
>  #-} 
>
> module CTNotes.P3Ch06c_MonoidalCats where
> import CTNotes.P1Ch08c_BiFunctorNonHask
> import Data.Void
> import Data.Kind (Type)

`category-extras`, `categories` define `Monoidal` in terms of more general type classes: 
`Associative`, `Bifunctor`, and `HasIdentity`.
This approach bundles the concept into one but is less generic.  
`i` plays the role of identity object, `bi` is the tensor product.

> class CBifunctor bi cat cat => Monoidal cat bi i | cat bi -> i where
>   associator :: cat (bi (bi a b) c) (bi a (bi b c))
>   lunitor :: cat (bi i a) a
>   runitor :: cat (bi a i) a

Using book notation, these correspond to
```
α_{a b c} :: (a ⊗ b) ⊗ c -> a ⊗ (b ⊗ c)
λ_a :: i ⊗ a -> a
ρ_a :: a ⊗ i -> a
```

```
ghci> :k Monoidal
Monoidal :: (k -> k -> *) -> (k -> k -> k) -> k -> Constraint
```

TODO: Add note about categorical coherence condition and show them in Haskell.


Instances
---------
Example: 
TODO `category-extras`, uses Void as Id for Product.  This does not seem right.

> instance Monoidal (->) (,) () where
>      associator = undefined  --TODO
>      lunitor = snd
>      runitor = fst

More famously (in pseudo-Haskell):  
```
instance Monoidal Endo Composition Identity
``` 
where `Endo` is category of Endofunctors on Hask, 
`Composition` is functor composition 
([N_P1Ch07_Functors_Composition](N_P1Ch07_Functors_Composition)), 
and `Identity` is the identity functor.


Non-Hask generalization
-----------------------
This is just a conceptual code and I have hard time implementing instances
but it conveys the message 
(a more implementable version is in [N_P3Ch12b_EnrichedPreorder](N_P3Ch12b_EnrichedPreorder))

> class NonHaskMonoidal (cat :: k -> k -> Type) where
>    type (a :: k) :*: (b :: k) :: k
>    type IdT :: k
>    nhbimap :: cat a c -> cat b d -> cat ( a :*: b) (c :*: d)
>    nhassociator :: cat (( a :*: b) :*: c) ( a :*: ( b :*: c))
>    nhlunitor :: cat (IdT :*: a) a
>    nhrunitor :: cat (a :*: IdT) a

([N_P3Ch12b_EnrichedPreorder](N_P3Ch12b_EnrichedPreorder) notes provide more examples).

|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch02a_LimitsColimitsExtras

CTFP Part 2 Chapter 1. Limits and Colimits - example from category-extras 
=========================================================================
Edward Kmett's, now obsolete, 
[category-extras](https://hackage.haskell.org/package/category-extras-0.53.5) 
package contains definition of limit and colimit for Haskell `Data.Functor` functors.  
I have linked the last nicely navigable hackage version of `category-extras`. 
That package is still a treasure trove except for its rule to
not exceed one line of explanation per typeclass and in most cases per module.

This note maps `category-extras` code definitions to the construction of limit and colimit presented in
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 2. Ch.1 Limits and Colimits](https://bartoszmilewski.com/2015/04/15/limits-and-colimits/).

> {-# LANGUAGE RankNTypes
>  , ExistentialQuantification 
>  , TypeOperators
>  #-}
>
> module CTNotes.P2Ch02a_LimitsColimitsExtras where
> import CTNotes.P1Ch10_NaturalTransformations ((:~>))
> import Data.Functor.Identity (Identity(..))
> import Data.Functor.Const (Const(..))

CTPF considers the general case of limits of functors __D:: I -> C__.  
These define a lot of interesting commuting diagrams in __D__.  Even if  __I__ is 
a very trivial (finite) category, this often generates quite interesting diagrams (pullback, equalizer, pushout). 
Unfortunately, these diagrams do not map easily to Haskell. For example, `MondadPlus` is 
not a pullback of `Monad` and `Alternative`, instead it defines its own `mzero` and `mplus`.  
(I think that this type of stuff is hard, maybe impossible for a programming language to support).   
This note focus is a more straightforward application of the limit concept, one that assumes `I = C = Hask`. 


Data.Functor Limit and universal quantification
----------------------------------------------
Using notation from the book, if we take `I = C = Hask` and `D = f`, where `f` is a `Data.Functor` functor, 
what would be the `Lim f`? (If one exists of course.)  
By definition, that would be a type `LimitF` (a regular kind `*` type) that has a nice 
natural transformation from `Const LimitF` to `f` 
```
type LimitF = ...
cone :: Const LimitF :~> f 
-- or isomorphically just
cone :: forall x. LimitF -> f x 
```
Consider ADT that looks like

> data FooBar x = NoX | AnotherNoX | SomeX x | AnotherSomeX x | Some2X x x

The only way to get a polymorphic function from something not dependent on `x` to `FooBar` is to use `NoX` or 
`AnotherNoX` data constructor.
I need a way to transform `FooBar` to a type that keeps constructors that 'do not depend on x'. 
For `FooBar`, that type would be (this is a regular type with no type variables):  

```
data LimitFooBar = NoX | AnotherNoX 
```

Fortunately, if type system supports universal quantification we can do just that. `category-extras` defines  

> type Limit f = forall a. f a 

(I read it as _keep the data constructors that do not depend on_ `a`)

What is cool about it is that `Limit` can be viewed as categorical formulation of universal quantification 
(ignoring complexity of ranks). 

__`Limit f` cone__  
It is easy to see that `Limit f` is an apex of a cone based on `f`:

> limitCone :: Limit f -> f x
> limitCone = id 

(This code says that if we have `f x` for all `x` we also have if for fixed `x`.
_That is the type application reduction rule in System F._)  
  
_Note:_ Currently, GHC (8.x) has problem with higher-rank type inference or
_impredicative polymorphism_ and this (more correct but isomorphic) declarations   
`limitCone :: Const (Limit f) x -> f x` or   
`limitCone :: Const (Limit f) :~> f` do not compile.  

TODO it would be good to understand this limitation better.

__Universality__:
Assume another type `c` with natural transformation 
`cone :: Const c :~> f`. This is equivalent to having a polymorphic function
`cone :: forall a . c' -> f a`.  We can easily factorize this (pseudo code of course):
```
factor :: c' -> Limit f
factor = cone
```
Parametricity enforces commutativity conditions, so indeed `Limit f` is the 
limit of `f` in the categorical sense.

HasLimit
--------
Since not all `Data.Functor` functors have limits `category-extras` includes

> class HasLimit f where
>   limit :: f a

The function `limit` returns a value that belongs to the `Limit f` type.  
Think of `limit` as a proof of type `Limit f`. To prove `Limit f`
you need to show that the type is inhabited. 

> instance HasLimit FooBar where
>   limit = NoX

In many cases the limit type is inhabited by only single value:

> instance HasLimit Maybe where
>   limit = Nothing
> instance HasLimit [] where
>	  limit = []

but this does not need to always be the case.

Intuitively, I view `Limit` as `(* -> *) -> *` type operator that strips all constructors
that depend to the parameter type.  A stricter view is that `Limit f` is a regular `*` 
type inhabited by values that all types `f a` have.


Limit as a Natural Isomorphism
------------------------------
Following the book (section with the same title)  
"A functor D from I to C has a limit Lim D if and only if there is a natural isomorphism between the two 
functors":

 C(b, Lim F) ≃ Nat(Δb, F)

(This formula says that factorizing morphisms are equivalent to
natural transformations that define the limit candidate `b`.)  
(Δb is constant functor maps all objects into b and all morphisms into id_b)

I can use it to derive `Limit f`.
Using pseudo Haskell:
```
Nat(Δb, F)  ==  --Haskell def on Natural Transformation
forall a . Const b a -> f a ~= -- def of Const and getConst isomorphism (see iso1a, iso1b)
forall a . b -> f a ~= -- b does not depend on a (see iso2a, iso2b)
b -> forall a . f a == -- def of Limit f
b -> Limit f  ==
C(b, Lim F)
```
Here are the isomorphisms from the above equational reasoning spelled out in Haskell:

> iso1a :: (forall a. Const b a -> f a) ->  (forall a. b -> f a)
> iso1a f = f . Const 
> iso1b :: (forall a. b -> f a) -> (forall a . Const b a -> f a)
> iso1b f = f . getConst
>
> iso2a :: (forall a . b -> f a) -> (b -> forall a . f a)
> iso2a = id
> iso2b :: (b -> forall a . f a) -> (forall a . b -> f a)
> iso2b = id


Non-Hask Categories, `Control.Arrow`
-----------------------------------
Seems that (at least morally) the above `Limit` definition 
```
type Limit f = forall a. f a
```
works for some non-Hask categories, in particular arrows (as defined in `Control.Arrow`,
see CTNotes.P1Ch08c_BiFunctorNonHask note).  
We would take `I = (->)`, `C = ar` (where `ar` represents arrow or some other non-`(->)` category defined on `*` types).

For arrows, as functor `f` we could consider `arr` itself 
(arrow laws require that `arr` is a functor) 
or `arr` composed with some functor `fa` `CFunctor ar ar fa` (see N_P1Ch07b_Functors_AcrossCats).

The problem is with writing expressions like (impredicative polymorphism limitations):
```
coneA :: ar (forall a . f a) f a
```
however if these were possible I would expect the arrowized versions of the above logic 
to work 
```
limitConeA :: Arrow ar => ar (forall a . f a) f x
limitConeA = id
```
given `coneA :: forall a . ar c (f a)` or `coneA :: forall a . ar (Const c x) (f x)` 
I should be able to write it as
`coneA :: ar c (forall a . f a)` which is the universal construction factorization I need.
To do stuff like this, there is a need to move between expressions `ar (Const c x) (f x)`
and `ar c (f a)`.  This is exactly the `iso1a`, `iso1b` above and is part of 
equational reasoning needed to show `C(b, Lim F) ≃ Nat(Δb, F)`.

This seems doable if the `ar :: * -> *` category satisfies some weak profunctor 
properties:

> class WeakProfunctor p where 
>   lmap :: (a -> b) -> p b c -> p a c
>
> iso1'a :: WeakProfunctor ar => (forall a. ar (Const b a) (f a)) -> (forall a. ar b (f a))
> iso1'a f = lmap Const f 
> iso1b' :: WeakProfunctor ar => (forall a. ar b (f a)) -> (forall a . ar (Const b a) (f a))
> iso1b' f = lmap getConst f 

So I believe, at least morally, the definition of `Limit` for Hask endofuntors 
extends to more general functors from Hask to some more exotic categories.

TODO this thinking could be expanded.

Functor Colimit
---------------
Reversing arrows give us this 'for free':

> data Colimit f = forall a. Colimit (f a)

Colimit uses existential quantification (`ExistentialQuantification` or `GADTs` pragma). 
Data constructor `Colimit` hides `a`:
```
:t Colimit
Colimit :: f a -> Colimit f
```

The Limit was very restrictive effectively intersecting values across all types `f a`, 
CoLimit is very permissive allowing any value from any type `f a`. 
Still `Colimit f` is just a
regular (not parametrized) type of kind `*`. That permissiveness allows for hiding of 
implementation details.   
Permissiveness is in construction 

> fooBar :: Colimit FooBar
> fooBar = Colimit $ SomeX 15

hiding is in the deconstruction

> inspect :: Colimit FooBar -> String
> inspect (Colimit NoX) = "NoX"
> inspect (Colimit AnotherNoX) = "AnotherNoX"
> inspect (Colimit (SomeX _)) = "SomeX ButNoClueWhich"
> inspect (Colimit (AnotherSomeX _)) = "AnotherSomeX ButNoClueWhich"
> inspect (Colimit (Some2X _ _)) = "Some2X ButNoClueWhich"

And that is mostly that.

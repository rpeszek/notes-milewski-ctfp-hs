|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch01a_LimitsColimitsExtras

CTFP Part 2 Chapter 1. Limits and Colimits - example from category-extras 
=========================================================================
Edward Kmett's `category-extras` package contains a straightforward defining of limit and colimit 
for Haskell `Data.Functor` functors.  
This note maps `category-extras` definitions to universal construction of limit presented in
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 2. Ch.1 Limits and Colimits](https://bartoszmilewski.com/2015/04/15/limits-and-colimits/).

> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE ExistentialQuantification #-}
> {-# LANGUAGE TypeOperators #-}

> module CTNotes.P2Ch01a_LimitsColimitsExtras where
> import CTNotes.P1Ch10_NaturalTransformations ((:~>))
> import Data.Functor.Identity (Identity(..))
> import Data.Functor.Const (Const(..))

CTPF considers the general case of limits of functors D:: I -> C.  
These define a lot of interesting commuting diagrams in D.  Even taking I to be 
a very trivial (finite) category often generates quite interesting diagrams (pullback, equalizer, pushout). 
Unfortunately, these diagrams do not map easily to Hask. For example, `MondadPlus` is 
not a pullback of `Monad` and `Monoid`, instead it defines its own `mzero` and `mplus`.
(Intuitively, I think that in nominally typed language this type of stuff is hard if not impossible).  
My focus in these notes is on learning and understanding of more direct/polymorphic 
applications of CT to the type system and programming. 

Data.Functor Limit
------------------
Using notation from the book, if we take `I = C = Hask` and `D = f`, where `f` is a `Data.Functor` functor, 
what would be the `Lim f`? (If one exists of course.)  
By definition, that would be a type `LimitF`in Hask (a regular kind `*` type) that has a nice 
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
For `FooBar`, that type would be (remember, this is a regular type, no type variables):  

```
data LimitFooBar = NoX | AnotherNoX 
```

Fortunately, if type system supports universal quantification we can do just that. `category-extras` defines  

> type Limit f = forall a. f a 

(I read it as _keep the data constructors that do not depend on_ `a`)  

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
Assume another type `C` with natural transformation 
`cone :: Const C :~> f`. This is equivalent to having a polymorphic function
`cone :: forall a . C' -> f a`.  We can easily factorize this (pseudo code of course):
```
factor :: C' -> Limit f
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

In many cases, however,
the limit type is inhabited by only single value:

> instance HasLimit Maybe where
>   limit = Nothing
> instance HasLimit [] where
>	  limit = []

Intuitively, I view `Limit` as `(* -> *) -> *` type operator that strips all constructors
that depend to the parameter type.  A stricter view is that `Limit f` is regular `*` 
type inhabited by values that all types `f a` have.


Limit as a Natural Isomorphism
------------------------------
Following the book (section with the title) existence of the following natural isomorphism can 
be viewed as a defining formula for Lim D:

 C(b, Lim F) ≃ Nat(Δb, F)

(This says that factorizing morphisms are equivalent to limit defining natural transformations.)  
I can use it to derive `Limit f`.
Using pseudo Haskell:
```
Nat(Δb, F)  ==  --Haskell def on Natural Transformation
forall a . Const b a -> f a ~= -- def of Const and getConst isomorphism 
forall a . b -> f a ~= -- b does not depend on a
b -> forall a . f a == -- def of Limit f
b -> Limit f  ==
C(b, Lim F)
```

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

If product was very restrictive effectively intersecting values across all types `f a`, 
coproduct is very permissive allowing any value from any type `f a`. Still `Colimit f` is just a
regular (not parametrized) type of kind `*`. That Permissiveness allows for hiding of 
implementation details.   
Permissiveness is in construction 

> fooBar :: Colimit FooBar
> fooBar = Colimit $ SomeX 15

hiding in deconstruction

> inspect :: Colimit FooBar -> String
> inspect (Colimit NoX) = "NoX"
> inspect (Colimit AnotherNoX) = "AnotherNoX"
> inspect (Colimit (SomeX _)) = "SomeX ButNoClueWhich"
> inspect (Colimit (AnotherSomeX _)) = "AnotherSomeX ButNoClueWhich"
> inspect (Colimit (Some2X _ _)) = "Some2X ButNoClueWhich"

And that is mostly that.

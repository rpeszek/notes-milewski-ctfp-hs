|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch01a_LimitsColimitsExtas

CTFP Part 2 Chapter 1. Limits and Colimits - example from category-extras 
=========================================================================
Edward Kmett `category-extras` package contains a straightforward defining of limit and colimit 
for Haskell `Data.Functor` functors.  
This note maps `category-extras` definitions to universal construction of limit presented in
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 2. Ch.1 Limits and Colimits](https://bartoszmilewski.com/2015/04/15/limits-and-colimits/).

> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE ExistentialQuantification #-}
> {-# LANGUAGE TypeOperators #-}

> module CTNotes.P2Ch01a_LimitsColimitsExtas where
> import CTNotes.P1Ch10_NaturalTransformations ((:~>))
> import Data.Functor.Identity (Identity(..))
> import Data.Functor.Const (Const(..))

Data.Functor Limit
------------------
Using notation from the book if we take `I = Hask`, `C = Hask` and `D = f` where `f` is a 'regular' Haskell functor
(`Data.Functor` functor), what would be the `Lim f`? (If one exists of course.)
We are looking for a type `LimitF` in Hask (not some type constructor but a regular kind `*` type) that has a nice 
natural transformation from `Const LimitF` to `f` 
```
type LimitF = ...
cone :: Const LimitF :~> f 
-- or isomorphically
cone :: forall x. LimitF -> f x 
```
Functor or not, consider ADT that looks like

> data FooBar x = NoX | AnotherNoX | SomeX x | AnotherSomeX x

The only way to get a cone from something not dependent on `x` to `FooBar` is to use `NoX` or `AnotherNoX` data constructor.
I need a way to form a type that keeps only constructors that 'do not depend on x'.  
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

Since not all `Data.Functor` functors have limits `category-extras` includes

> class HasLimit f where
>   limit :: f a
> instance HasLimit Maybe where
>   limit = Nothing
> instance HasLimit [] where
>	  limit = []

Colimit TODO
------------

> data Colimit f = forall b. Colimit (f b)

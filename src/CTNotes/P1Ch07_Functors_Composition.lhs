WORK IN PROGRESS

CTFP Part 1 Chapter 7. Functors. Fuctor Compostion.
=============================================================

Last section of Fuctor chapter talks about compostion of functors and about how functors themselves can be viewed
as morphisms in another category.
This is my attempt to use haskell to describe these concepts.
These notes assume familiarty with CTFP upto and including Ch 7.

> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE PolyKinds #-}
>
> module CTNotes.P1Ch07_Functors_Composition where

Short recap to set the stage:
----------------------------
Functors are structure preseverning mappings between categories. Functors themselves are morphism
in a 'higher' categpry like Cat.
Functors in Haskell are really endofunctors on Hask category. They map types to types (a to f a)
and functions to functions (fmap:: (a -> b) -> f a -> f b).  They are supposed to be structure preseving but
Haskell leaves it to the programmer to prove that aspect.
Hask is a category in which objects are types and morphisms are regular functions between these types.
For regular functions inputs and outputs are values/terms.
If you restrict functors to their action on Hask objects (types) only, tbe functor inputs and outputs for functors are types.
Functors are 'type-level' functions and in practice are type constructors such as List, Maybe, Either r, (r ->), etc.

Type level programming can be type checked, only the types of types are called kinds.
If we forget about strucure preseving fmap functors have kind * -> *.
Funtor typeclass defined in Data.Functor can be viewed as having kind signature (* -> *) -> Constraint.

Functor Composition
-------------------
Indentity functor is introduced in Chapter 8. Here is that definiton repeated:

> newtype Identity a = Identity a
> instance Functor Identity where
>     fmap f (Identity x) = Identity (f x)

we also can use Haskell to define functor composition (book uses G ∘ F notation).
The trick is simplar to how Indentity functor is defined. We need to construct a type that wraps composed type constructors

> newtype FCompose f g a = FCompose { getFComp :: f (g a) }
> instance (Functor f, Functor g) => Functor (FCompose f g) where
>    fmap f (FCompose x) = FCompose (fmap (fmap f) x)

so instead of direct composition like ```Maybe [a]``` we have ```FCompose Maybe [] a``` which is clearly isomorphic
(by adding and removing FCompose constructor).

Now we can create a type operator (using TypeOperators pragma).  I am using colon (:) prefix to make it clear that this is a type
level operator.

> type f :. g = FCompose f g

This way ```Maybe :. []``` becomes a functor that maps Int into Maybe [Int].

Category Laws
-------------
Thus far we have provided code for indentity and composition. It is not that surprising that these do satisfy category laws.
The composition is associative (up to isomorphism because FCompose data constructor will need to move around):

> iso1 :: Functor f => ((f :. g) :. h) a -> (f :. (g :. h)) a
> iso1 (FCompose (FCompose fgh_x)) = FCompose (fmap FCompose fgh_x)
>
> iso2 :: Functor f => (f :. (g :. h)) a -> ((f :. g) :. h) a
> iso2 (FCompose f_comp_ghx) =  FCompose (FCompose $ fmap getFComp f_comp_ghx)

Simple equational reasoning shows that iso1 and iso2 are indeed inverses of one another.
For example:
```
 iso2 . iso1 $ FCompose (FCompose fgh_x)                   ==  -- definition of iso1
 iso2 $ FCompose (fmap FCompose fgh_x)                     ==  -- definition of iso2
 FCompose (FCompose $ fmap getFComp (fmap FCompose fgh_x)) ==  -- functors preserve morphism composition
 FCompose (FCompose $ fmap (getFComp . FCompose) fgh_x)    ==  -- getFComp deconstructs FCompose
 FCompose (FCompose $ fmap id fgh_x)                       ==  -- functors presever identity morphims
 FCompose (FCompose fgh_x)
```

Left and right identity laws follow from simplar reasoning.
We have 2 ingeredients needed to a 'higher' category. Can we do a bit more?

Type contract
----------------------
Haskell base contains Category typeclass defined in Control.Category module which allows to express what it
means to be a category:

```
class Category cat where
     id :: cat a a
     (.) :: cat b c -> cat a b -> cat a c

instance Category (->) where ...
instance Cateogry (:~:) where ...

```
This is perfect for defining categories when objects are types.
Besides expressing the fact that something is a category we have the benefit of type checking of id and composition.
Proof obligation of checking the laws is left to the programmer.


To do something analougus, we need to lift ourselves one level up.
If 'normal' categories are about types and functions, out category needs to be about kinds and functors.
I use KCategory name to indicate that.  Haskell TypeFamilies pragma allows me to define a contract analogous to
Control.Category.Category.

> class KCategory cat where
>    type KId cat :: * -> *
>    type KComp cat :: (* -> *) -> (* -> *) -> * -> *

With Control.Category.Category typeclass the benefit is typechecking id and composition.  Now the benefit is kind-checking
of id and composition that act on types instead of values.  Notice that this is less typed then the prvious case.
For example id :: cat a a guarantees that 'a' is the same, we no longer have such guarantee.

Our Category
------------
Functor domain and co-domain are types of kind *.  We can think of this category as monoid with one object and lots of morphisms.

> data OurCategory = OurCategory

> instance KCategory OurCategory where
>    type KId OurCategory = Identity
>    type KComp OurCategory = FCompose

TODO can we do even better than kind check? PolyKinds?

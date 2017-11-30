|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch05a_YonedaAndMap

__Work-in-progress__


Notes about CTFP Part 2 Chapter 5. Yoneda Lemma and fmap
========================================================
This note is about what helped me internalize Yoneda from the programming point of view.

Book ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 2. Ch.5 Yoneda Lemma](https://bartoszmilewski.com/2015/09/01/the-yoneda-lemma/).

> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE ScopedTypeVariables #-}
>
> module CTNotes.P2Ch05a_YonedaAndMap where
> import CTNotes.P1Ch10_NaturalTransformations((:~>))

Yoneda in Hask
--------------
Yoneda Lemma can be viewed, by a programmer, as a stronger version of `fmap`. 
The great news is that this strength is there for free.
Yoneda Lemma states (in pseudo-Haskell, ~= represents type level isomorphism) that
```
Functor f => f a ~= forall x. (a -> x) -> f x
```
Lets start with __one direction__:
```
yoneda_1 :: Functor f => f a -> forall x. (a -> x) -> f x
```
This is preety much, `fmap`
```
fmap :: Functor f => (a -> x) -> f a -> f x
```
Here are both, spelled out in English:   

`fmap`    : for a given value `fa` of type `f a` and function `a -> x` I can produce value of type `f x`.  
`yoneda_1`: for a given value `fa` of type `f a` and function `a -> x` I can produce value of type `f x`.  

If it walks like a duck ...

I will show the details too.  
To define `yoneda_1` I just need to flip the arguments on `fmap` and notice that `fmap` is a perfectly polymorphic function

> fmap_1 :: Functor f => f a -> ((a -> x) -> f x)
> fmap_1 = flip fmap  
>
> yoneda_1 :: Functor f => f a -> forall x. (a -> x) -> f x
> yoneda_1 = fmap_1

or using NT definition from [N_NaturalTransformations](N_NaturalTransformations) 

> yoneda_1' :: Functor f => f a -> ((->) a :~> f)
> yoneda_1' = fmap_1

To get `yoneda_2` in the __other direction__, I need to look at `forall x. (a -> x) -> f x` and understand what it is.
It looks close to a _Continuation Passing Style_ computation and, as programmer, I would like to use it as such.
I need to pass a function to it and the code writes itself, giving me only one polymorphic option, the `id`. 

> yoneda_2 :: Functor f => (forall x. (a -> x) -> f x) -> f a
> yoneda_2 trans = trans id
> -- or
> yoneda_2' :: Functor f => ((->) a :~> f) -> f a
> yoneda_2' trans = trans id

In Type Theoretical lambda terms, this applies type `a` to quantification `forall x`. This is like a function application 
only at type level. In psedo-Haskell that would look like `(forall x) $ a` resulting in `a`.    
In Category Theoretical terms, this picks the component of the natural transformation at object `a`. 
That component starts at the hom-set `C(a,a)` (`a -> a` in Hask), 
`id` is the point value on which that component operates.


Equational reasoning in pseudo-Haskell shows that these are indeed isomorphic
(current impredicative polymorphism limitations prevent from using GHC to do much of this)
```
(yoneda_2 . yoneda_1) :: Functor f => f a -> f a

(yoneda_2 . yoneda_1) fa 
== (\t -> t id) . (flip fmap $ fa)
== (flip fmap $ fa) id 
== fmap id fa 
== id -- because f is functor

(yoneda_1 . yoneda_2) :: Functor f => ((->) a :~> f) -> ((->) a :~> f)

(yoneda_1 . yoneda_2) trans 
==  ((flip fmap) . (\t -> t id)) trans 
==  (flip fmap) (trans id) 
== (\f -> fmap f (trans id)) 
== (\f -> trans (fmap f id)) -- naturality *
== (\f -> trans (f . id)) -- definition of reader (->) functor
== (\f -> trans f) 
== trans
```

Equality marked with `*` is the naturality condition applied to `id :: a -> a` 

```
fmap f . trans == trans . fmap f
   
                trans
      (a -> x) ------->  f x
         ^                ^
         |                |
  fmap f |                | fmap f
         |                |
      (a -> a) ------->  f a
                trans
```


Co-Yoneda in Hask
-----------------
Co-Yoneda states that:
```
Functor f => f a ~= forall x . (x -> a) -> f x
```

This has the same (dual) similarity to `fmap`
```
F a ~= forall x . (x -> a) -> f x
coyoneda_2 :: (forall x . (x -> a) -> f x) -> f a

fmap :: Functor f => (x -> a) -> f x -> f a
```

and is based on the contravariant end of the reader functor.
 

Yoneda with no Hask categories
------------------------------
Can we get some of the same goodness for functors `F :: C -> Hask`, where `C` is a non-Hask category
such as some discrete category ([N_P1Ch03c_DiscreteCat](N_P1Ch03c_DiscreteCat)) or a simple finite category 
created with GADTs ([N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats), [N_P1Ch03c_Equalizer](N_P1Ch03c_Equalizer))?
I am doubtful.

In Hask natural transformations are simply polymorphic functions `forall x. f x -> g x`, with
other categories this is not as nice but this aspect seems doable ([N_P1Ch03c_Equalizer](N_P1Ch03c_Equalizer)).

The breaking point is the hom-set. For endofunctor `F:: Hask -> Hask` the hom-set functor used in Yoneda Lemma is 
the Reader functor `(->)` and there is no nice equivalent like that for no-Hask categories. 
For example, for discrete categories the hom-set would be a singleton for `Discrete(a,a)` hom-set and `Void` 
for everything else.  
Whatever type equivalence can be achieved in these cases, I think it will be ugly. 


TODO examples (maybe a separate file)

  
 

|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch05a_YonedaAndMap

__Work-in-progress__


Notes about CTFP Part 2 Chapter 5. Yoneda Lemma and fmap
========================================================
This note is about what helped me internalize Yoneda from the programming point of view.  
It is about how (Co)Yoneda relates to `fmap` on the conceptual and practical level.
This note also includes some equational reasoning proofs to supplement more book's more 
general mathematical approach. 

Book ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 2. Ch.5 Yoneda Lemma](https://bartoszmilewski.com/2015/09/01/the-yoneda-lemma/).

> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE ExistentialQuantification #-}
> {-# LANGUAGE GADTs #-}
>
> module CTNotes.P2Ch05a_YonedaAndMap where
> import CTNotes.P1Ch10_NaturalTransformations((:~>))

Yoneda in Hask
--------------
As a programmer, I view Yoneda Lemma as a stronger version of `fmap`. 
The great news is that this strength is there for free.
Yoneda Lemma states (in pseudo-Haskell, ~= represents type isomorphism) that
```
Functor f => f a ~= forall x. (a -> x) -> f x
```
Yoneda says that `fmap` is (in some sense) an isomorphism.  
Lets start with __one direction__:
```
yoneda_1 :: Functor f => f a -> forall x. (a -> x) -> f x
```
This is pretty much, `fmap`
```
fmap :: Functor f => (a -> x) -> f a -> f x
```
Here are both, spelled out in English:   

`fmap`    : for a given value `fa` of type `f a` and function `a -> x` I can produce value of type `f x`.  
`yoneda_1`: for a given value `fa` of type `f a` and function `a -> x` I can produce value of type `f x`.  

If it walks like a duck ...  
The power of squinting!

I will show the details next.  
To define `yoneda_1` I just need to flip the arguments on `fmap` and notice that `fmap` is a perfectly polymorphic function

> fmap_1 :: Functor f => f a -> ((a -> x) -> f x)
> fmap_1 = flip fmap  
>
> yoneda_1 :: Functor f => f a -> forall x. (a -> x) -> f x
> yoneda_1 = fmap_1
>
> -- or
>
> yoneda_1' :: Functor f => f a -> ((->) a :~> f)
> yoneda_1' = fmap_1

To get `yoneda_2` in the __other direction__, I need to look at `forall x. (a -> x) -> f x` and understand what it is.
It looks close to a _Continuation Passing Style_ computation and, as programmer, I would like to use it as such.
I need to pass a function to it. The code writes itself, giving me only one option, the `id`. 

> yoneda_2 :: (forall x. (a -> x) -> f x) -> f a
> yoneda_2 trans = trans id
> -- | or
> yoneda_2' :: ((->) a :~> f) -> f a
> yoneda_2' trans = trans id

In Type Theoretical lambda terms, this applies type `a` to quantification `forall x`. This is like a function application 
only at type level. In psedo-Haskell that would look like `(forall x) $ a` resulting in `a`.    
In Category Theoretical terms, this picks the component of the natural transformation at object `a`. 
That component starts at the hom-set `C(a,a)` (`a -> a` in Hask), 
`id` is the point value on which that component operates.  
A very helpful intuition from the book, for me, was that Yoneda allows me to pick any value of type `f a` 
when transforming `id` and there rest is uniquely determined by the naturality conditions.

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
As stated in the book, Yoneda is not just isomorphism it is also natural in both `f` and `a`.  
TODO is naturality of Yoneda represented somehow in programming? 


Co-Yoneda in Hask
-----------------
The book defines Co-Yoneda as 
```
Functor f => f a ~= forall x . (x -> a) -> f x
```
which corresponds directly to Nat(C(-, a), F) ≅ F a. 

Most libraries such as scalaz or `category-extras`, `kan-extensions` in Haskell 
use the following, co-limit based, definition of CoYoneda (in pseudo-Haskell):
```
Functor f => f a ~= exists x . (x -> a) -> f x
```
I am focusing on the second definition.  

There is an equivalent (dual) similarity to `fmap`
```
F a ~= exists x . (x -> a) -> f x
coyoneda_2 :: (exists x . (x -> a) -> f x) -> f a

fmap :: Functor f => (x -> a) -> f x -> f a
```
In Haskell CoYoneda is defined as
 
> data CoYoneda f a = forall x. CoYoneda (x -> a) (f x)
> -- | or
> data CoYoneda' f a = forall x. CoYoneda' ((x -> a) -> f x)

(`CoYoneda` data constructor hides x making it existential)  
or in GADT style (which I find the cleanest)

> data CoYoneda'' f a where
>    CoYoneda'' :: (x -> a) -> f x -> CoYoneda'' f a

and the corresponding isomorphisms would look like this (notice duality to Yoneda):

> coyoneda_1 :: f a -> CoYoneda'' f a
> coyoneda_1 = CoYoneda'' id
>
> coyoneda_2 :: Functor f => CoYoneda'' f a -> f a
> coyoneda_2 (CoYoneda'' f fa) = fmap f fa


(Co)Yoneda Functor instance
---------------------------
Following definitions in `category-extras` or `kan-extensions` package I can define 

> newtype Yoneda f a = Yoneda { runYoneda :: forall x. ((a -> x) -> f x) } 

what is interesting is that `(Co)Yoneda` type constructors get `fmap` for free

> instance Functor (Yoneda f) where
>  	fmap f y = Yoneda (\k -> (runYoneda y) (k . f))
> instance Functor (CoYoneda'' f) where
> 	fmap f (CoYoneda'' x2a fx) = CoYoneda'' (f . x2a) fx

(The proof obligations follow from properties of function composition)  
they also nicely preserve other properties like Monad or Applicative instances.


Yoneda with no-Hask categories
------------------------------
Can we get some of the same goodness for functors `F :: C -> Hask`, where `C` is a non-Hask category
such as some discrete category ([N_P1Ch03c_DiscreteCat](N_P1Ch03c_DiscreteCat)) or a simple finite category 
created with GADTs ([N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats), [N_P1Ch03c_Equalizer](N_P1Ch03c_Equalizer))?
I am doubtful.

In Hask natural transformations are simply polymorphic functions `forall x. f x -> g x`, with
other categories this is not as nice but this aspect seems doable ([N_P1Ch03c_Equalizer](N_P1Ch03c_Equalizer)).

The breaking point is the hom-set. With `C = Hask` the hom-set functor used in Yoneda Lemma is 
the Reader Functor `(->)`. There is no nice equivalent like that for no-Hask categories. 
For example, for discrete categories the hom-set would be a Unit `()` for `Discrete(a,a)` and `Void` 
for everything else.  
Whatever type equivalence can be achieved in these cases, I think it will be ugly. 


Code Examples
-------------
__Performance__  Functional code often ends up with lots of `fmap` calls.  For recursive data structures
such as trees or lists `fmap` can be expensive. It is beneficial to use functor law
`fmap f . fmap g == fmap f . g` to fuse composition of `fmap`-s into one big `fmap` of composed functions.
Careful look at `fmap` definitions for `(Co)Yoneda` shows that this is exactly what is going on.

`CoYoneda` has the additional benefit of running the `fmap` in the 
`coyoneda_2 :: Functor f => CoYoneda f a -> f a` transformation and not in `coyoneda_1 :: f a -> CoYoneda f a`
Thus, wrapping up a big computation inside `CoYoneda` can lead to significant performance optimization.

I imagine this to be especially true in languages like Scala which do not have lambda like code rewriting rules.   
This blog post shows how this plays out in Haskell: 
http://alpmestan.com/posts/2017-08-17-coyoneda-fmap-fusion.html.

__DSLs__ Functor for free benefit allows to remove functor requirement on the design of 
abstract DSL instruction set (on the DSL algebra).
 
Ref Haskell: http://comonad.com/reader/2011/free-monads-for-less-2/  
Ref Scala: http://blog.higher-order.com/blog/2013/11/01/free-and-yoneda/
  
__CPS__ the simplified version of Yoneda `forall x. ((a -> x) -> x)` is the type of
_Continuation Passing Style_ computation and that is obviously used a lot.

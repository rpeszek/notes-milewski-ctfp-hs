|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch05a_YonedaAndMap

__Work-in-progress__


Notes about CTFP Part 2 Chapter 5. Yoneda Lemma and `fmap`
=========================================================
This note is about what helped me internalize Yoneda from the programming point of view.  
It is about how (Co)Yoneda relates to `fmap` on the conceptual and practical level.
This note also includes some equational reasoning proofs to supplement the more 
general, mathematical approach in the book. 

Book ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 2. Ch.5 Yoneda Lemma](https://bartoszmilewski.com/2015/09/01/the-yoneda-lemma/).

> {-# LANGUAGE RankNTypes 
>  , TypeOperators
>  , ScopedTypeVariables
>  , ExistentialQuantification
>  , GADTs 
>  #-}
>
> module CTNotes.P2Ch05a_YonedaAndMap where
> import CTNotes.P1Ch10_NaturalTransformations((:~>))

Yoneda Lemma
------------
As a programmer, I view Yoneda Lemma as a stronger version of `fmap`. 
This includes
* Iso nature of `fmap`-s
* Free `fmap`-s
* Faster `fmap`-s

The great news is that this strength is there for free.
Yoneda Lemma states (in pseudo-Haskell, ~= represents type isomorphism) that
```
Functor f => f a ~= forall x. (a -> x) -> f x
```
Yoneda says that `fmap` is (in some sense) an isomorphism.  
Lets start with __one direction__:
```
toYoneda :: Functor f => f a -> forall x. (a -> x) -> f x
```
This is pretty much, `fmap`
```
fmap :: Functor f => (a -> x) -> f a -> f x
```
Here are both, spelled out in English:   

`fmap`: for a given value `fa` of type `f a` and function `a -> x`, I can produce value of type `f x`.  
`toYoneda`: for a given value `fa` of type `f a` and function `a -> x`, I can produce value of type `f x`.  

If it walks like a duck ...  
The power of squinting!

__The details:__  
To define `toYoneda` I just need to flip the arguments on `fmap` and notice that `fmap` is a perfectly polymorphic function

> fmap' :: Functor f => f a -> ((a -> x) -> f x)
> fmap' = flip fmap  
>
> toYoneda :: Functor f => f a -> forall x. (a -> x) -> f x
> toYoneda = fmap'
> -- or
> toYoneda' :: Functor f => f a -> ((->) a :~> f)
> toYoneda' = fmap'

To get `fromYoneda` in the __other direction__, I need to look at `forall x. (a -> x) -> f x` and understand what it is.
It looks close to a _Continuation Passing Style_ computation and I would like to use it as such.
I need to pass a function to it. The code writes itself giving me only one option: the `id`. 

> fromYoneda :: (forall x. (a -> x) -> f x) -> f a
> fromYoneda trans = trans id
> -- | or
> fromYoneda' :: ((->) a :~> f) -> f a
> fromYoneda' trans = trans id

In type theoretical lambda terms, this applies type `a` to quantification `forall x`. This is like a function application 
only at type level. In psedo-Haskell that would look like `(forall x) $ a` resulting in `a`.    
In category theoretical terms, this picks the component of the natural transformation at object `a`. 
That component starts at the hom-set `C(a,a)` (`a -> a` in Hask), 
`id` is the point value on which that component operates.  
A very helpful intuition from the book, for me, was that Yoneda allows me to pick any value of type `f a` 
when transforming `id` and there rest is uniquely determined by the naturality conditions.

Equational reasoning in pseudo-Haskell shows that these are indeed isomorphic
(current impredicative polymorphism limitations prevent from using GHC to do much of this)
```
(fromYoneda . toYoneda) :: Functor f => f a -> f a

(fromYoneda . toYoneda) fa 
== (\t -> t id) (flip fmap $ fa)
== (flip fmap $ fa) id 
== fmap id fa 
== id -- because f is functor

(toYoneda . fromYoneda) :: Functor f => ((->) a :~> f) -> ((->) a :~> f)

(toYoneda . fromYoneda) trans 
== ((flip fmap) . (\t -> t id)) trans 
== (flip fmap) (trans id) 
== (\f -> fmap f (trans id)) 
== (\f -> trans (fmap f id)) -- naturality *
== (\f -> trans (f . id)) -- definition of reader (->) functor
== (\f -> trans f) 
== trans
```
Equality marked with `*` is the naturality condition applied to `id :: a -> a` 
```
fmap f . trans == trans . fmap f  
f :: a -> x
   
                trans
      (a -> x) ------->  f x
         ^                ^
         |                |
  fmap f |                | fmap f
         |                |
      (a -> a) ------->  f a
                trans
```
As stated in the book, Yoneda is not just isomorphism, it is also natural in both `f` and `a`.  
Naturality of Yoneda translates to polymorphism in programming.  But there could be something deeper
about it too, I DUNNO.


Co-Yoneda
---------
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
('co' also reverses the quantification).  
I am focusing on the second definition. Existential quantification makes this one quite intuitive, 
more so than the original, universally quantified, Yoneda.  

There is an equivalent (dual) similarity to `fmap`
```
F a ~= exists x . (x -> a) -> f x
fromCoYoneda :: (exists x . (x -> a) -> f x) -> f a

fmap :: Functor f => (x -> a) -> f x -> f a
```
In Haskell CoYoneda is defined as
 
> data CoYoneda f a = forall x. CoYoneda (x -> a) (f x)

(`CoYoneda` data constructor hides x making it existential)  
or in GADT style (which I find the cleanest)

> data CoYoneda' f a where
>    CoYoneda' :: (x -> a) -> f x -> CoYoneda' f a

and the corresponding isomorphisms would look like this (notice duality to Yoneda):

> toCoYoneda :: f a -> CoYoneda' f a
> toCoYoneda = CoYoneda' id
>
> fromCoYoneda :: Functor f => CoYoneda' f a -> f a
> fromCoYoneda (CoYoneda' f fa) = fmap f fa


Functor instances - free `fmap`
-------------------------------
Following definitions in `category-extras` or `kan-extensions` package I can define 

> newtype Yoneda f a = Yoneda { runYoneda :: forall x. ((a -> x) -> f x) } 

what is interesting is that `(Co)Yoneda` type constructors get to be functors for free

> instance Functor (Yoneda f) where
>  	fmap f y = Yoneda (\k -> (runYoneda y) (k . f))
> instance Functor (CoYoneda' f) where
> 	fmap f (CoYoneda' x2a fx) = CoYoneda' (f . x2a) fx

(The proof obligations follow from properties of function composition)  
they also nicely preserve other properties like Monad or Applicative instances.

There is a nice categorical explanation why (Co)Yoneda gives free `fmap` that is based on Kan extensions
(see [N_P3Ch11a_KanExt](N_P3Ch11a_KanExt) and the book [P3. Ch 11](https://bartoszmilewski.com/2017/04/17/kan-extensions/)).


Code Examples
-------------
__Performance - faster `fmap` with CoYoneda__  Functional code often ends up with lots of `fmap` calls.  
For recursive data structures such as trees or lists `fmap` can be expensive. It is beneficial to use functor law
`fmap f . fmap g == fmap f . g` to fuse composition of `fmap`-s into one big `fmap` of composed functions.
Careful look at `fmap` definitions for `(Co)Yoneda` shows that this is exactly what is going on.

`CoYoneda` has the additional benefit of running the `fmap` in the 
`fromCoYoneda :: Functor f => CoYoneda f a -> f a` transformation and not in `toCoYoneda :: f a -> CoYoneda f a`.
People call it deferred `fmap`.
Thus, wrapping up a big computation inside `CoYoneda` can lead to significant performance optimization.

I imagine this to be especially true in languages like Scala which do not have lambda like code rewriting rules.    

The following trivial example is simplified version of: 
http://alpmestan.com/posts/2017-08-17-coyoneda-fmap-fusion.html

> withCoYoneda :: Functor f => (CoYoneda' f a -> CoYoneda' f b) -> f a -> f b
> withCoYoneda comp = fromCoYoneda . comp . toCoYoneda
>
> stupid :: (Functor f, Num a) => f a -> f a
> stupid = fmap (*2) . fmap (+1) . fmap (^2)
> 
> smarter = fmap ((*2) . (+1) . (^2))
>
> bigSum1a = sum $ stupid $ [1..1000000]
> bigSum1b = sum $ smarter $ [1..1000000]
> bigSumCoY = sum $ withCoYoneda stupid  $ ([1..1000000])

ghci output:
```bash
ghci> :set +s
ghci> bigSum1a
666667666669000000
(1.95 secs, 938,081,272 bytes)
ghci> bigSum1b
666667666669000000
(1.61 secs, 826,081,816 bytes)
ghci> bigSumCoY
666667666669000000
(1.61 secs, 858,082,656 bytes)
```
This will not measure up to lambda optimization of something like `Vector` but it is nice.

__DSLs__ Functor for free benefit allows to remove functor requirement on the design of 
abstract DSL instruction set (on the DSL algebra).
 
Ref Haskell: http://comonad.com/reader/2011/free-monads-for-less-2/  
Ref Scala: http://blog.higher-order.com/blog/2013/11/01/free-and-yoneda/
  
__CPS__. the simplified version of Yoneda `forall x. ((a -> x) -> x)` is the type of
_Continuation Passing Style_ computation and that is obviously used a lot.

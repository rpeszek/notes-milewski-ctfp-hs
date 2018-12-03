|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch10b_NTsNonHask

Notes about natural transformations on non-Hask categories
=========================================================
Natural transformation definition 
(`type f :~> g = forall x. f x -> g x`) is kind polymorphic and is applicable to 
Functors from non-Hask categories.  
This formula assumes that the destination category is Hask `(->)`.
This note shows that the naturality condition free theorem is no longer true.

There is another formula worth studying, for a general category `cat` the natural transformation
could be defined as `type NatTran cat f g = forall x. cat (f x) (g x)` following the Ends formula
(see previous note).  Investigation of this definition is a TODO.
 
Book ref:
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 10. Natural Transformations](https://bartoszmilewski.com/2015/04/07/natural-transformations/).

> {-# LANGUAGE GADTs
>  , DataKinds
>  , KindSignatures
>  , FlexibleInstances
>  , PolyKinds
>  , MultiParamTypeClasses
>  , FlexibleContexts
>  , TypeOperators
>  , StandaloneDeriving
>  #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module CTNotes.P1Ch10b_NTsNonHask where
> import Control.Category 
> import Prelude(Show)
> import CTNotes.P1Ch10_NaturalTransformations ((:~>))
> import CTNotes.P1Ch07b_Functors_AcrossCats (CFunctor, cmap, Process2(..))


Example why naturality is not for free
--------------------------------------

Natural transformations (:~>) defined in 
[N_P1Ch10_NaturalTransformations](N_P1Ch10_NaturalTransformations) are kind-polymorphic
```
ghci> :k (:~>)
(:~>) :: (k -> *) -> (k -> *) -> *
```
So it make sense to use them with non-Hask source categories, such as categories I have defined in 
[N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats).

However, restricting `forall` quantification to some small kind results in
`forall x. f x -> g x` being not strong enough to have naturality condition as a free theorem.

__Counterexample__
Consider very simple category `A -> B`.

> data Object = A | B 
>
> data HomSet (a :: Object) (b :: Object) where
>    MorphId :: HomSet a a    -- polymorphic data constructor (in a)
>    MorphAB :: HomSet 'A 'B
>
> deriving instance Show (HomSet a b)
>
> compose :: HomSet b c -> HomSet a b -> HomSet a c
> compose MorphId mab  = mab      
> compose mbc MorphId =  mbc     
>
> instance Category HomSet where
>   id = MorphId
>   (.) = compose

and a simple functor which maps objects `A` to `Process 'A` and `B` to `Process 'B`

> data Process (o :: Object) where
>     PStart1 ::  Process 'A
>     PStart2 ::  Process 'A
>     PEnd1   ::  Process 'A -> Process 'B
>     PEnd2   ::  Process 'A -> Process 'B
>
> deriving instance Show (Process o)
>
> instance CFunctor Process HomSet (->) where
>    cmap MorphId x = x
>    cmap MorphAB PStart1 = PEnd1 PStart1
>    cmap MorphAB PStart2 = PEnd2 PStart2

As a type, `Process` allows any of these morphisms:
```
  Start1 --> End1 
        \  /\    
         \/       
         /\      
        /  \/    
  Start2 --> End2
``` 
However the above functor instance just picks these 2 morphisms
```
  Start1 --> End1 

  Start2 --> End2
``` 
(Notice possible `CFunctor` instances that make different picks)  

Counterexample:

> badNt :: Process :~> Process
> badNt (PEnd2 x) = (PEnd1 x)
> badNt (PEnd1 x) = (PEnd2 x)
> badNt x = x
> 
> naturality1 = cmap MorphAB . badNt 
> naturality2 = badNt . cmap MorphAB

```
ghci> naturality1 PStart1
PEnd1 PStart1
ghci> naturality2 PStart1
PEnd2 PStart1
```
_square box_


How to think about this
-----------------------
For `forall (x::k). f x -> g x` to be a natural transformation for non-Hask source categories 
requires additional proof obligation of naturality condition.  This type is now too permissive. 
Naturality is a value level equality similar in nature to many other laws. 

As indicated in [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats) there could be several very different functor instances
for a given type constructor.  This tells me that the type constructors `f :: k -> *` themselves do not 
embody their functoriality well.  Thus, we should not expect that we get functorial properties 
automatically from type expressions that just use `f` (like the `forall (x::k). f x -> g x` expression).
A polymorphic function may play nice with one of the functors but not with all of them.

Last being the best:  free theorems are based on parametricity which is rooted on not being 
able to recover type information. GADT defines a very small space of possible morphisms. 
Pattern matching on these effectively recovers type information.  Parametricity is lost.

Here is answer to my question form Bartosz Milewski:
"Free theorems are the result of parametricity, which is a property of the language rather than a category. 
In simple words, parametricity means that we define a polymorphic function using a single 
formula for all types. As soon as you allow pattern-matching on types, you lose parametricity."

And here is quote from the book chapter itself:  
"The reason it works in Haskell is because naturality follows from parametricity. 
Outside of Haskell, though, not all diagonal sections across such hom-sets 
will yield natural transformations."

Some of this goodness can come back when dealing with functors from finite categories to finite categories
([N_P3Ch06b_FiniteMonads](N_P3Ch06b_FiniteMonads)).

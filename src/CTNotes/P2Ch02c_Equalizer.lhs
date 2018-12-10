|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch03c_Equalizer

Note about CTFP Part 2 Chapter 2. Limits - Equalizer. 
=====================================================
Note about representing equalizer in Haskell.  
This is not going to end well. The goal is to see how far I can go with it before it breaks.  
The exercise is to try to follow 
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 3. Limit and Colimits](https://bartoszmilewski.com/2015/04/15/limits-and-colimits/).
using Equalizer and Haskell code.

> {-# LANGUAGE GADTs 
>  , DataKinds 
>  , KindSignatures 
>  , FlexibleInstances 
>  , PolyKinds 
>  , MultiParamTypeClasses 
>  , Rank2Types 
>  #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module CTNotes.P2Ch02c_Equalizer where
> import Control.Category 
> import Prelude(undefined, ($))
> import Data.Functor.Const (Const(..))
> import CTNotes.P1Ch07b_Functors_AcrossCats (CFunctor, cmap)

A => B Category
----------------
This approach is constructed in a way similar to [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats). 
 
> data Object = A | B
>
> data HomSet (a :: Object) (b :: Object) where
>    MorphId :: HomSet a a    -- polymorphic data constructor (in a)
>    MorphAB1 :: HomSet 'A 'B
>    MorphAB2 :: HomSet 'A 'B
>
> compose :: HomSet b c -> HomSet a b -> HomSet a c
> compose MorphId mab  = mab     
> compose mbc MorphId =  mbc     

Cool! GHC knows that this pattern match is exhaustive.  I love it!

__A => B Category is Haskell category__  
Similarly to [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats) I get:

> instance Category HomSet where
>   id = MorphId
>   (.) = compose


Functors `A => B` to `Hask` 
---------------------------
I am using imported definition of `CFunctor` from [N_P1Ch07b_Functors_AcrossCats](N_P1Ch07b_Functors_AcrossCats)
(similar to `category-extras` package).  Here it is for reference:
```
class (Category r, Category s) => CFunctor f r s  where
   cmap :: r a b -> s (f a) (f b)
```

__Const functor__  
[N_P1Ch07b_Functors_AcrossCats](N_P1Ch07b_Functors_AcrossCats) provided instance of imported 
`Const` (`Data.Functor.Const`) that works polymorphically for any source Category

Here is a proof that it works here (this compiles):

> test :: Const a (x :: Object) -> Const a (x :: Object)
> test = cmap MorphId


__Embedding functor ('D' functor)__  
To create a functor from `A => B` to Hask I simply need to pick
2 fixed types `a` and `b`, and two functions `a -> b`

> data PickType a b (o :: Object) where
>    First :: a -> PickType a b 'A
>    Second :: b -> PickType a b 'B
>
> getFirst :: PickType a b 'A -> a
> getFirst (First x) = x

Note, `getFirst` patter match is exhaustive. 

> data PickFun a b (o :: Object) = Pick {
>      f1:: a -> b
>      , f2:: a -> b
>      , value:: PickType a b o
>    }

`PickFun a b` is the 'D' functor:

> applyF1 :: PickFun a b 'A  -> PickFun a b 'B
> applyF1 x = let v = (f1 x) ((getFirst . value $ x)) in x { value = Second v }
>
> applyF2 ::  PickFun a b 'A  -> PickFun a b 'B
> applyF2 x =  let v = (f2 x) ((getFirst . value $ x)) in x { value = Second v }
>
> instance CFunctor (PickFun a b) HomSet (->) where
>   cmap MorphId  = \x -> x        
>   cmap MorphAB1 = applyF1 
>   cmap MorphAB2 = applyF2 

(Some ugly non-lens code indeed.)  
We have `Const` and `D` functors needed in the construction of the cone.


Cone and natural transformations 
--------------------------------
Given two (fixed) functions `fn1 :: a -> b`, `fn2: a -> b`, cone is simply two functions from `c` to either end of `a -> b`:

> type Cone a b c = (c -> a, c -> b)

Naive steal from [N_P2Ch02a_LimitsColimitsExtras](N_P2Ch02a_LimitsColimitsExtras) suggests to define
natural transformation between `Const c` and `PickFun a b` as

> -- Not what I want
> type NatTran0 a b c = forall (x :: Object). Const c x -> PickFun a b x

this type contains polymorphic functions that do not depend on `x :: Object`. 
Instead, I want a product type one that knows which `x` is used
(using a poor man's singleton approach)

> data Sing (a:: Object) where
>    IsA :: Sing 'A
>    IsB :: Sing 'B
>    
> type NatTran a b c = forall (x::Object). Sing x -> Const c x -> PickFun a b x

At this point I ignore the naturality condition.

We know from the book that cones and natural transformations are isomorphic.  
Here is how this plays out in this special case (showing only one iso):

> iso1 :: (a -> b) -> (a -> b) -> Cone a b c -> NatTran a b c
> iso1 fn1 fn2 (c1, c2) IsA = \cx -> Pick fn1 fn2 ((First . c1 . getConst) cx)
> iso1 fn1 fn2 (c1, c2) IsB = \cx -> Pick fn1 fn2 ((Second . c2 . getConst) cx)

(Read this as: given 2 fixed functions `f1`, `f2` we can establish iso from `Cone` to `NatTran`.)

Type checking the code we just know that arrows point at correct objects. We do not know if the cone diagrams
actually commute
```
 fn1 . c1 = fn2 . c1 = c2  
```
(or that the naturality condition is satisfied - which should be the same thing) 
this would have to be a proof obligation left to the programmer and that obligation is the pudding.


Dead stop
---------
It was clear from the beginning that this journey is hopeless.  
Even if Haskell provided ability for me to supply proof that diagrams commute, 
finding the limit would be next step where, again, I would have no clue how to proceed.  
With `Hask -> Hask` endofunctors limit is 'guessed' and constructed using  
universal quantification.  There is a higher rank type that does the trick. 
It does not seem to be a good uniform guess like this here. 

I read that an equalizer problem called 'Post Correspondence Problem' is undecidable. 
It is about checking if equalizer of 2 group homomorphisms is not empty.

Computing equalizers seems to be related to finding if 2 functions are equivalent
and this is undecidable as well.

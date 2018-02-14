|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch05b_YonedaNonHask

Notes about CTFP Part 2 Chapter 5. Yoneda Lemma for non-Hask categories
=======================================================================
This note explores Yoneda Lemma for functors on non-Hask categories in Haskell. 

I use a simple GADT construction (from [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats)) of the category `A->B=>C` 
that enumerates all possible morphisms.
As we know ([N_P1Ch07b_Functors_AcrossCats](N_P1Ch07b_Functors_AcrossCats)) functors from such categories are not unique. 
We also know ([N_P2Ch10b_NTsNonHask](N_P2Ch10b_NTsNonHask)) that the naturality condition is no longer automatically satisfied.

However, examining Yoneda on such categories does provides a nice intuition. 
To implement functors on these simple GADT categories, I have to pattern match on all morphisms.
Yoneda Lemma can be partially observed by reordering of that pattern match and grouping it on the functor data constructors.
Each data constructor ends up matched with a polymorphic function that goes to every `f x`.

Book ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 2. Ch.5 Yoneda Lemma](https://bartoszmilewski.com/2015/09/01/the-yoneda-lemma/).

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE Rank2Types #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module CTNotes.P2Ch05b_YonedaNonHask where
> import Control.Category 
> import Prelude(undefined, ($), flip)
> import Data.Functor.Const (Const(..))
> import CTNotes.P1Ch07b_Functors_AcrossCats (CFunctor, cmap, Process2(..))
> import qualified CTNotes.P1Ch03b_FiniteCats as A_B__C


Generalized Yoneda Definition
-----------------------------
As discussed in [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats), 
standard `Category` typeclass is kind-polymorphic allowing for instances other than Hask itself.
The following definition is quoted from `Control.Category` with added explicit kind signature:
```
class Category (homset:: k -> k -> *) where
     id :: homset a a
     (.) :: homset b c -> homset a b -> homset a c
```
Notice that `homset a b` lives in Hask (`*`) even if `a` and `b` are of some (potentially) different kind `k`.
Using book notation, that corresponds to __C(a,b)__ being an object in __Set__ for some (other than __Set__) category 'C'. 
In Haskell, this can be used with `DataKinds` to create custom categories like I did in 
[N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats)
 
Here is a generalized definition of Yoneda type constructor with explicit kind signature 
(I use `CYoneda` name to mimic `CFunctor`): 

> newtype CYoneda (homset :: k -> k -> *) (f :: k -> *) a = 
>      CYoneda { runCYoneda :: forall x. (homset a x -> f x) } 

(`x` is inferred as `x :: k`).


Functor Instance
----------------
As discussed in [N_P1Ch07b_Functors_AcrossCats](N_P1Ch07b_Functors_AcrossCats), Haskell
can express functors between different categories (a quote, not an actual code):
```
class (Category homset, Category s) => CFunctor f homset s  where
   cmap :: homset a b -> s (f a) (f b)
```

`CYoneda` is (still) a functor for free:

> instance (Category homset) => CFunctor (CYoneda homset f) homset (->) where
>    cmap f y = CYoneda (\k -> (runCYoneda y) (k . f))

Note `(k . f)` happens in the `homset` category, 
but, the code is exactly the same as in the Hask version ([N_P2Ch05a_YonedaAndMap](N_P2Ch05a_YonedaAndMap))


Isomorphism
-----------
Again, the code is not any different than Hask ([N_P2Ch05a_YonedaAndMap](N_P2Ch05a_YonedaAndMap))

> toCYoneda :: CFunctor f homset (->) => f a -> CYoneda homset f a
> toCYoneda fa = CYoneda $ flip cmap $ fa
>  
> fromCYoneda :: (Category homset) => CYoneda homset f a -> f a 
> fromCYoneda y = (runCYoneda y) id

except the proof that `toYoneda . fromYoneda = id` uses the naturality condition which may not be true any more 
(and it looks like it typically is not, see [N_P1Ch10b_NTsNonHask](N_P1Ch10b_NTsNonHask)).
However, `fromYoneda . toYoneda = id` uses only functor laws which agrees with the intuition that
there could be some polymorphic functions that fail the naturally test 
(`CYoneda homset f a` is bigger and contains image of `f a`).


Pattern Match Intuition for Yoneda
----------------------------------
Consider the `A -> B => C` category from [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats) and example functors from 
[N_P1Ch07b_Functors_AcrossCats](N_P1Ch07b_Functors_AcrossCats).

My goal is to explore impact Yoneda makes on construction of `cmap` for such functors.  
`cmap` implementations pattern match on all `A -> B => C` morphisms.
Yoneda becomes visible by simply reordering that pattern match and grouping it by the functor data constructors! 

Consider, for example, `Process2` (repeated from [N_P1Ch07b_Functors_AcrossCats](N_P1Ch07b_Functors_AcrossCats)
that uses category A->B=>C with objects A, B, C, generated by 3 not trivial morphisms MorphAB, MorphBC1, MorphBC2

`Process2` type expresses process with possible transformations:
```
   Start1 --> Mid1 --->  End2
         \  /\     \  /\
          \/        \/
          /\        /\
         /  \/     /  \/ 
   Start2 --> Mid2 ---> End2
```
CFunctor instance for Process2 maps `A -> B => C` to these transformations
```
  Start1 --> Mid1 --->  End2
                  \  /\
                   \/
                   /\
                  /  \/ 
  Start2 --> Mid2 ---> End2              
```
Clearly the type has more freedom of movement than the functor image. 
There will be polymorphic functions that won't play nice with the functor 
(see [N_P1Ch10b_NTsNonHask](N_P1Ch10b_NTsNonHask)).
However we can still 'pick' only the good choices that satisfy the naturality condition.    

Instead of proceeding with functor implementation from 
[N_P1Ch07b_Functors_AcrossCats](N_P1Ch07b_Functors_AcrossCats)
I reorder the pattern match and look at value constructors of `Process2 a`, say 
P2Start1 (which has type `Process2 'A_B__C.A`), I will get: 

```
instance CFunctor Process2 A_B__C.HomSet (->) where
   cmap A_B__C.MorphId  P2Start1 = P2Start1        -- HomSet 'A 'A -> Process2 'A 
   cmap A_B__C.MorphAB  P2Start1 = P2Mid1 P2Start1 -- HomSet 'A 'B -> Process2 'B 
   cmap A_B__C.MorphAC1 P2Start1 = P2End1 . P2Mid1 $ P2Start1  -- HomSet 'A 'C -> Process2 'C 
   cmap A_B__C.MorphAC2 P2Start1 = P2End2 . P2Mid1 $ P2Start1  -- HomSet 'A 'C -> Process2 'C 
   ...
```
This pattern match is a polymorphic case expression of type `homset a x -> f x` defined for all `x`-s 
(this time I offer a real type checked code to verify my claim):

> cmapForP2Start1 :: Process2 'A_B__C.A -> 
>                    forall (x :: A_B__C.Object) . A_B__C.HomSet 'A_B__C.A x -> 
>                    Process2 x  
> cmapForP2Start1 P2Start1 morph = case morph of
>                     A_B__C.MorphId  -> P2Start1
>                     A_B__C.MorphAB  -> P2Mid1 P2Start1
>                     A_B__C.MorphAC1 -> P2End1 . P2Mid1 $ P2Start1
>                     A_B__C.MorphAC2 -> P2End2 . P2Mid1 $ P2Start1
> cmapForP2Start1 P2Start2 morph = undefined

Repeating what I already said, `forall (x :: A_B__C.Object) . A_B__C.HomSet 'A_B__C.A x -> Process2 x` contains more 
functions than I will use in my definition of `cmap`.  This is because there are some bad polymorphic functions that 
do not play nice with my functor.  For example, the following is a perfectly polymorphic choice not consistent with the functor:

> badChoice :: Process2 'A_B__C.A -> 
>              forall (x :: A_B__C.Object) . A_B__C.HomSet 'A_B__C.A x -> 
>              Process2 x  
> badChoice P2Start1 morph = case morph of
>                     A_B__C.MorphId  -> P2Start1
>                     A_B__C.MorphAB  -> P2Mid2 P2Start1  -- uses P2Mid2
>                     A_B__C.MorphAC1 -> P2End1 . P2Mid1 $ P2Start1  -- uses P2Mid1
>                     A_B__C.MorphAC2 -> P2End2 . P2Mid1 $ P2Start1
> badChoice P2Start2 morph = undefined


CoYoneda 
--------
Existentially quantified version of CoYoneda for non-Hask hom-sets:

> data CCoYoneda (homset :: k -> k -> *) (f :: k -> *) a where
>    CCoYoneda :: homset x a -> f x -> CCoYoneda homset f a

These remain virtually unchanged from ([N_P2Ch05a_YonedaAndMap](N_P2Ch05a_YonedaAndMap)) 
(however, the accumulating `(f . x2a)` composition happens in `homset` category):

> instance (Category homset) => CFunctor (CCoYoneda homset f) homset (->)  where
> 	cmap f (CCoYoneda x2a fx) = CCoYoneda (f . x2a) fx
>
> toCoYoneda :: (Category homset) => f a -> CCoYoneda homset f a
> toCoYoneda = CCoYoneda id
>
> fromCoYoneda :: CFunctor f homset (->) => CCoYoneda homset f a -> f a
> fromCoYoneda (CCoYoneda f fa) = cmap f fa

I expect the opposite conclusion that `CCoYoneda homset f a` can be 'smaller' that `f a`

I see no good __co-intuitions__ about `cmap` construction.  
I think, that is because, unlike Yoneda, CoYoneda uses `cmap` 'on the way out'.   
(Compare `toCoYoneda` with `toYoneda` which is basically `cmap`, 
also see notes on the strong relationship between Yoneda and map in 
[N_P2Ch05a_YonedaAndMap](N_P2Ch05a_YonedaAndMap).)


Practical use?
--------------
Is questionable. 
Compared to Hask [N_P2Ch05a_YonedaAndMap](N_P2Ch05a_YonedaAndMap):     

* Since we no longer have strict type isomorphism the usefulness needs to be questioned
* CoYoneda benefit of deferred `cmap` is the same as for Hask case 
* Functor for free benefit is the same as in Hask.   
* I do not know about any DSL construction with non-Hask categories at this moment. 



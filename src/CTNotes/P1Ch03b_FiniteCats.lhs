|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch03b_FiniteCats

Note about CTFP Part 1 Chapter 3. Examples of categories.  Finite category construction in Haskell.
===================================================================================================
Haskell representation of categories created from simple directed graphs (finite enumeration of objects and morphisms).
I use `DataKinds` to encode category objects as types (of a custom kind) and enumerate
all possible morphisms using a GADT.  Using GADTs makes it simple to visualize what is going on because I use them
to enumerate al possible morphisms.

The approach looks generic (should be easily adjusted to other finite categories) 
but I am not trying to do it polymorphically (if that is even possible).  
I am just using a simple example category `A->B=>C`. 
(Free category generated by from simple graph with objects `A`, `B`, `C` and 3 generating morphisms: 
one `A -> B` and two `B -> C`). 

Because this construction allows for pattern matching on morphisms, it 
also allows to implicitly infer type information. Prametricity is lost and so are free theorems.

This approach is similar to [Natural Numbers note N_P1Ch03a_NatsCat](N_P1Ch03a_NatsCat).  
 
This note supplements _Simple Graphs_ section of [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 3](https://bartoszmilewski.com/2014/12/05/categories-great-and-small/) with somewhat 'advanced' Haskell.

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE StandaloneDeriving #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE AllowAmbiguousTypes #-}  --needed for FinCategory instance only
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module CTNotes.P1Ch03b_FiniteCats where
> import Control.Category 
> import Prelude(Show, undefined)

Simple Finite Category
----------------------
All objects in `A->B=>C` are defined as data type 
 
> data Object = A | B | C deriving Show

and promoted (`DataKinds` pragma) to a kind `Object` with types `A` `B` and  `C`.  
Category objects will be the types `A` `B` and  `C`.
 
All morphism in `A->B=>C` are defined using the following GADT 

> data HomSet (a :: Object) (b :: Object) where
> -- generating edges in A->B=>C
>    MorphId :: HomSet a a    -- polymorphic data constructor (in a)
>    MorphAB :: HomSet 'A 'B
>    MorphBC1 :: HomSet 'B 'C   
>    MorphBC2 :: HomSet 'B 'C 
> -- derived 
>    MorphAC1 :: HomSet 'A 'C -- MorphCB1 . MorphAB
>    MorphAC2 :: HomSet 'A 'C -- MorphCB2 . MorphAB
>
> deriving instance Show (HomSet a b)
>
> newtype CoHomSet b a = CoHomSet (HomSet a b)
>
> deriving instance Show (CoHomSet a b)
  
Morphism composition:  

> compose :: HomSet b c -> HomSet a b -> HomSet a c
> compose MorphId mab  = mab      -- GHC knows b == c
> compose mbc MorphId =  mbc      -- GHC knows a == b
> compose MorphBC1 MorphAB = MorphAC1
> compose MorphBC2 MorphAB = MorphAC2

Cool! GHC knows that this pattern match is exhaustive, something that takes a minute to digest.
When writing this, I just needed to think about free construction cases.

_Note_: I have assume free construction approach, `MorphAC1` and `MorphAC2` are different.
If, instead, I created a GADT with one `MorphAC` and have defined 
```
compose MorphBC1 MorphAB = MorphAC
compose MorphBC2 MorphAB = MorphAC 
```
This would have been an equalizer-like diagram and it would be very hard to functor it into Hask.  
Explicitly enumerating all possible morphisms in a GADT looks like redundant coding, but
it provides flexibility to play with different category designs. 


__`A->B=>C` is `Control.Category`:__  
Here is the definition of `Category` quoted from base package `Control.Category` module: 
```
class Category cat where
       id :: cat a a
       (.) :: cat b c -> cat a b -> cat a c
```

`PolyKinds` pragma causes `Category` to infer most general kind on `cat` which is `k -> k -> *`
so `Category` class automatically infers `Object -> Object -> *` for me matching HomSet kind signature.  
From the categorical stand point, `cat :: Object -> Object -> *` acts as a hom-set and `Hask` acts as
the __Set__ category.  A better name would be 'Hom-Hask'.    

> instance Category HomSet where
>   id = MorphId
>   (.) = compose

Expressions like  `MorphCB . MorphAB`  will not compile, but 'correct' compositions work fine:

```bash
ghci> :t MorphId . MorphAB
MorphId . MorphAB :: HomSet 'A 'B

ghci> :t MorphBC1 . MorphAB
MorphBC1 . MorphAB :: HomSet 'A 'C
```

It is quite amazing that you can do stuff like this. 
Generalizing use of categories instead of just hardcoding Hask everywhere seems like an interesting direction.

A Better Alternative
--------------------
`HomSet` uses polymorphic definition of _id_ morphisms `MorphId`.  This is sometimes convenient by does not work well 
if there is a need to isolate the object on which _id_ works on.  (No pattern matching on types.)  
The following definition could be a better for finite categories like the `A->B=>C`.

> data ObjectRep (a :: Object) where
>    ARep :: ObjectRep 'A  
>    BRep :: ObjectRep 'B 
>    CRep :: ObjectRep 'C 
>
> deriving instance Show (ObjectRep a)
>
> data HS (a :: Object) (b :: Object) where
>    MoId :: ObjectRep a -> HS a a    -- non-polymorphic version
>    MoAB :: HS 'A 'B
>    MoBC1 :: HS 'B 'C   
>    MoBC2 :: HS 'B 'C 
>    MoAC1 :: HS 'A 'C -- MorphCB1 . MorphAB
>    MoAC2 :: HS 'A 'C -- MorphCB2 . MorphAB
>
> deriving instance Show (HS a b)
> 
> comp :: HS b c -> HS a b -> HS a c
> comp (MoId _) mab  = mab      
> comp mbc (MoId _) =  mbc      
> comp MoBC1 MoAB = MoAC1
> comp MoBC2 MoAB = MoAC2

Except, I no longer get the polymorphic id:

> instance Category HS where
>   id = undefined
>   (.) = comp

but I could consider something similar to the definition of `HaskEnrichedCategory` 
in [N_P3Ch12b_EnrichedPreorder](N_P3Ch12b_EnrichedPreorder).

> class FinCategory (ob :: k -> *) (cat:: k -> k -> *) where
>   finid :: ob a -> cat a a
>   fincomp :: cat b c -> cat a b -> cat a c
>
> instance FinCategory ObjectRep HS where
>   finid = MoId
>   fincomp = comp


Functors
--------
[N_P1Ch07b_Functors_AcrossCats](N_P1Ch07b_Functors_AcrossCats) provides example functors from this category. 


Parametricity is lost
---------------------
See [N_P1Ch10b_NTsNonHask](N_P1Ch10b_NTsNonHask) 

Possibly relevant:
[Retricted Parametricity](https://www.cs.kent.ac.uk/people/staff/dao7/drafts/tfp-structures-orchard12.pdf)

TODO should I add value level representation of this? Does not seem to be needed.

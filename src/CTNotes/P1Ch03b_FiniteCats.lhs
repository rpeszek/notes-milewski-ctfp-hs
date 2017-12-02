|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch03b_FiniteCats

Note about CTFP Part 1 Chapter 3. Examples of categories.  Finite category construction in Haskell.
===================================================================================================
Haskell representation of categories created from simple directed graphs (finite enumeration of objects and morphisms).
I use a dependently typed approach to encode category objects as types (of a custom kind) and enumerate
all possible morphisms using a GADT. 

The approach looks generic (should be easily adjusted to other finite categories) 
but I am not trying to do it polymorphically (if that is even possible).  
I am just using a simple example category `A->B=>C`. 
(Free category generated by from simple graph with objects `A`, `B`, `C` and 3 generating morphisms: 
one `A -> B` and two `B -> C`). 

This approach is very similar to [Natural Numbers note N_P1Ch03a_NatsCat](N_P1Ch03a_NatsCat).

This note supplements _Simple Graphs_ section of [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 3](https://bartoszmilewski.com/2014/12/05/categories-great-and-small/) with somewhat 'advanced' Haskell.

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE PolyKinds #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module CTNotes.P1Ch03b_FiniteCats where
> import Control.Category 
> import Prelude()

Simple Finite Category
----------------------
All objects in `A->B=>C` are defined as data type 
 
> data Object = A | B | C

and promoted (`DataKinds` pragma) to a kind `Object` with types `A` `B` and  `C`.  
Category objects will be the types `A` `B` and  `C`.
 
All morphims in `A->B=>C` are defined using the following GADT 

> data HomSet (a :: Object) (b :: Object) where
> -- generating edges in A->B=>C
>    MorphId :: HomSet a a    -- polymorphic data constructor (in a)
>    MorphAB :: HomSet 'A 'B
>    MorphBC1 :: HomSet 'B 'C   
>    MorphBC2 :: HomSet 'B 'C 
> -- derived 
>    MorphAC1 :: HomSet 'A 'C -- MorphCB1 . MorphAB
>    MorphAC2 :: HomSet 'A 'C -- MorphCB2 . MorphAB
  
  
Morphism composition:

> compose :: HomSet b c -> HomSet a b -> HomSet a c
> compose MorphId mab  = mab      -- GHC knows b == c
> compose mbc MorphId =  mbc      -- GHC knows a == b
> compose MorphBC1 MorphAB = MorphAC1
> compose MorphBC2 MorphAB = MorphAC2

Cool! GHC knows that this pattern match is exhaustive, something that takes a minute to digest.
When writing this, I just needed to think about free construction cases.

__`A->B=>C` is `Control.Category`:__  
Here is the definition of `Category` quoted from base package `Control.Category` module: 
```
class Category cat where
       id :: cat a a
       (.) :: cat b c -> cat a b -> cat a c
```

`PolyKinds` pragma causes `Category` to infer most general kind on `cat` which is `k -> k -> *`
so `Category` class automatically infers `Object -> Object -> *` for me matching HomSet kind signature.     

> instance Category HomSet where
>   id = MorphId
>   (.) = compose

Expressions like  `MorphCB . MorphAB`  will not compile, but other compositions work fine:

```bash
ghci> :t MorphId . MorphAB
MorphId . MorphAB :: HomSet 'A 'B

ghci> :t MorphBC1 . MorphAB
MorphBC1 . MorphAB :: HomSet 'A 'C
```

It is quite amazing that you can do stuff like this in Haskell. 
Generalizing use of categories instead of just hardcoding Hask everywhere seems like a good thing.

TODO should I add value level representation of this?

|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch07b_Functors_AcrossCats

Note about CTFP Part 1 Chapter 7. Functors on non-Hask categories 
==================================================================
This note explores generalized definition of Functor typeclass that works with other categories
than Hask.  
It also provides some example Functors for the category `A->B=>C` defined in 
[N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats).

Book ref:
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 7](https://bartoszmilewski.com/2015/01/20/functors/)

> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE FlexibleContexts #-}
>
> module CTNotes.P1Ch07b_Functors_AcrossCats where
> import Data.Functor.Const (Const(..))
> import Control.Category 
> import Prelude(undefined, ($))
> import qualified CTNotes.P1Ch03b_FiniteCats as FinCat


`categories` (`Control.Categorical.Functor`) and `category-extras` (`Control.Functor.Categorical`) 
define `CFunctor` (quoted code):
```
class (Category r, Category s) => CFunctor f r s | f r -> s, f s -> r where
  cmap :: r a b -> s (f a) (f b)
```
(Taken from `category-extras`, `categories` just call it `Functor`)

Ignoring functional dependencies I define non-endofunctors as:

> class (Category r, Category s) => CFunctor f r s  where
>    cmap :: r a b -> s (f a) (f b)

With `PolyKinds` in place this assumes most generic kinds for `r` and `s`, `r :: k1 -> k1 -> *`
`r :: k2 -> k2 -> *`. That makes the definition usable with non-Hask categories like the categories
I created in [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats) or [N_P1Ch03a_NatsCat](N_P1Ch03a_NatsCat)

Here is one polymorphic instance:

> instance (Category r) => CFunctor (Const a) r (->) where
>   cmap _ (Const v) = Const v

`Const` is defined (imported from `Data.Functor.Const` base package) as 
```
newtype Const a b = Const { getConst :: a }

λ> :k Const
Const :: * -> k -> *
```

`PolyKinds` keeps kind of `b` polymorphic but the destination category has to have objects of kind `*` 
(it does not need to be `(->)`).  

I was able to define instance of `CFunctor` polymorphically (in `r`) because `Const` does not care about source category.
I am using (->) for destination, because this is what the implementation `\Const v -> Const v` uses.

To show that this works, I use category defined in the imported notes [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats).

> test :: Const a (x :: FinCat.Object) -> Const a (x :: FinCat.Object)
> test = cmap FinCat.MorphId

But this would not compile:

```
-- Bad code
test :: Const a (x :: FinCat.Object) -> Const a (x :: FinCat.Object)
test = cmap FinCat.MorphAB
```
 
Functor Examples
----------------

This example splits object `FinCat.C` into 2 possible endings of the same type `Process1 'FinCat.C`

> data Process1 (o :: FinCat.Object) where
>     P1Start ::  Process1 'FinCat.A
>     P1Mid   ::  Process1 'FinCat.A -> Process1 'FinCat.B
>     P1End1  ::  Process1 'FinCat.B -> Process1 'FinCat.C
>     P1End2  ::  Process1 'FinCat.B -> Process1 'FinCat.C
>
> instance CFunctor Process1 FinCat.HomSet (->) where
>    cmap FinCat.MorphId   = \x -> x
>    cmap FinCat.MorphAB   = P1Mid 
>    cmap FinCat.MorphBC1  = P1End1 
>    cmap FinCat.MorphBC2  = P1End2 
>    cmap FinCat.MorphAC1  = P1End1 . P1Mid  
>    cmap FinCat.MorphAC2  = P1End2 . P1Mid 

This example collapses morphisms leading to the end type `Process2 'FinCat.C`

> data Process2 (o :: FinCat.Object) where
>     P2Start1 ::  Process2 'FinCat.A
>     P2Start2 ::  Process2 'FinCat.A
>     P2Mid1   ::  Process2 'FinCat.A -> Process2 'FinCat.B
>     P2Mid2   ::  Process2 'FinCat.A -> Process2 'FinCat.B
>     P2End1   ::  Process2 'FinCat.B -> Process2 'FinCat.C
>     P2End2   ::  Process2 'FinCat.B -> Process2 'FinCat.C
>   
> instance CFunctor Process2 FinCat.HomSet (->) where
>    cmap = go  
>        where
>            step1 :: Process2 'FinCat.A -> Process2 'FinCat.B
>            step1 P2Start1 = P2Mid1 P2Start1
>            step1 P2Start2 = P2Mid2 P2Start2
>            go :: FinCat.HomSet a b -> Process2 a -> Process2 b      
>            go FinCat.MorphId  =  \x -> x
>            go FinCat.MorphAB  = step1 
>            go FinCat.MorphBC1  = P2End1 
>            go FinCat.MorphBC2  = P2End2 
>            go FinCat.MorphAC1  = P2End1 . step1  
>            go FinCat.MorphAC2  = P2End2 . step1 

A more involved example of a Tree where leafs are marked with `FinCat.A`, single branches with `FinCat.B`, 
and double branches with `FinCat.A`. Branches can be of any type so, for example, `A -> B -> B -> B` is valid.
The image in `Hask` is reacher allowing for more flexibility.

> data Tree (o :: FinCat.Object) where 
>     Leaf :: Tree 'FinCat.A
>     Down :: Tree o -> Tree 'FinCat.B
>     Branch :: Tree o1 -> Tree o2 -> Tree 'FinCat.C
> 
> instance CFunctor Tree FinCat.HomSet (->) where
>    cmap = go  
>        where
>          right = Branch Leaf
>          left = \t -> Branch t Leaf
>          go :: FinCat.HomSet a b -> Tree a -> Tree b      
>          go FinCat.MorphId   = \x -> x
>          go FinCat.MorphAB   = Down 
>          go FinCat.MorphBC1  = right
>          go FinCat.MorphBC2  = left
>          go FinCat.MorphAC1  = right . Down 
>          go FinCat.MorphAC2  = left . Down

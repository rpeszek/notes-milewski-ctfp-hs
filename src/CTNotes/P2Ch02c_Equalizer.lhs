|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch03c_Equalizer

__ Work in progress __

Note about CTFP Part 2 Chapter 2. Limits - Equalizer. 
=====================================================
Representing Equalizer in Haskell.  
This is not going to end well. The goal is to see how far I can go with it and where it breaks.  

Book reference: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 3](https://bartoszmilewski.com/2015/04/15/limits-and-colimits/).

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> 
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

> module CTNotes.P2Ch02c_Equalizer where

> import Control.Category 
> import Prelude(undefined, ($))
> import Data.Functor.Const (Const(..))


A => B Category
----------------
This approach follows construction in [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats). 
 
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

__This Haskell `Control.Category` category:__  
Here is the definition of `Category` quoted from base package `Control.Category` module: 
```
class Category cat where
       id :: cat a a
       (.) :: cat b c -> cat a b -> cat a c
```

A => B Category is Haskell category

> instance Category HomSet where
>   id = MorphId
>   (.) = compose


Functors `A => B` to `Hask` 
---------------------------
Ref: https://hackage.haskell.org/package/category-extras-0.53.5/docs/Control-Functor-Categorical.html
```
class (Category r, Category s) => CFunctor f r s | f r -> s, f s -> r where
  cmap :: r a b -> s (f a) (f b)
```

Ignoring functional dependencies I define non-endofunctors as:

> class (Category r, Category s) => CFunctor f (r :: k -> k -> *) s  where
>    cmap :: r a b -> s (f a) (f b)

__Const functor__   
is easy (this is using `Const` definition form base `Data.Functor.Const`):

> instance CFunctor (Const a) HomSet (->) where
>   cmap _ (Const v) = Const v

Note polymorphic kinds at work. `Const` is defined as 
```
newtype Const a b = Const { getConst :: a }

λ> :k Const
Const :: * -> k -> *
```
and here it automatically uses `b` of kind `Object`.


__Embedding functor__  
I need 2 fixed types `a` `b` and two morphisms `a -> b` in Hask

> data PickVal a b (o :: Object) where
>    First :: a -> PickVal a b 'A
>    Second :: b -> PickVal a b 'B
>
> getFirst :: PickVal a b 'A -> a
> getFirst (First x) = x

Note, `getFirst` is exhaustive patter match. 

> data PickFun a b (o :: Object) = Pick {
>      f1:: a -> b
>      , f2:: a -> b
>      , value:: PickVal a b o
>    }

With some ugly non-lens code I managed to define the second functor needed 
for the equalizer:

> applyF1 :: PickFun a b 'A  -> PickFun a b 'B
> applyF1 x = let v = (f1 x) ((getFirst . value $ x)) in x { value = Second v }
>
> applyF2 ::  PickFun a b 'A  -> PickFun a b 'B
> applyF2 x =  let v = (f2 x) ((getFirst . value $ x)) in x { value = Second v }
>
> instance CFunctor (PickFun a b) HomSet (->) where
>   cmap MorphId  = \x -> x        -- Pick f1 f2
>   cmap MorphAB1 = applyF1 
>   cmap MorphAB2 = applyF2 




TODO this is still hopeless, but think more

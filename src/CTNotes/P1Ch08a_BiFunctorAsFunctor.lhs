|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch08a_BiFunctorAsFunctor

Notes about CTFP Part 1 Chapter 8. BiFunctor as CFunctor and Product Category
=============================================================================
The book introduced CT concept of bifunctor as simply a functor from a product category __C x C -> D__.  
This note expresses one side of this equivalence in Haskell as an exercise:
```
instance (CFunctor f ((->) :**: (->)) (->)) =>  Bifunctor (Curry f)
```
The hard part is implementing product category so the code can express (->) :**: (->) or `Hask :**: Hask`.
Unfortunately, presented `:**:` does not implement `Control.Category` `id` because of 
a type arity strictness. 

Book ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 1. Ch.8 Functoriality](https://bartoszmilewski.com/2015/02/03/functoriality/).
 
> {-# LANGUAGE TypeFamilies, TypeOperators, GADTs, FlexibleContexts, PolyKinds, UndecidableInstances, InstanceSigs #-}
>
> module CTNotes.P1Ch08a_BiFunctorAsFunctor where
> import Control.Category
> import Prelude hiding ((.), id)
> import CTNotes.P1Ch07b_Functors_AcrossCats
 
Following the `data-category` package https://hackage.haskell.org/package/data-category-0.7
I define product of categories (I am using a more relaxed kind signature) as:  
 
> data (:**:) :: (k -> k -> *) -> (k -> k -> *) -> * -> * -> * where
>    (:**:) :: c1 a1 b1 -> c2 a2 b2 -> (:**:) c1 c2 (a1, a2) (b1, b2)

(this is a GADT that defines type parametrized by pairs, this causes problems with implementation of `id`
which wants to see `cat a a`, not `cat (a,b) (a,b)`).
So instance of `Control.Category` is only partially implemented: 

> instance (Category c1, Category c2) => Category (c1 :**: c2) where
>    id = undefined -- id :**: id  
>    (a1 :**: a2) . (b1 :**: b2) = (a1 . b1) :**: (a2 . b2)
 
Definition of BiFunctor from the book:
 
> class Bifunctor f where
>      bimap :: (a -> c) -> (b -> d) -> f a b -> f c d
>      bimap g h = first g . second h
>      first :: (a -> c) -> f a b -> f c b
>      first g = bimap g id
>      second :: (b -> d) -> f a b -> f a d
>      second = bimap id

with 2 examples copied for a reference:
 
> instance Bifunctor (,) where
>     bimap :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
>     bimap g h (a,b) = (g a, h b)
>  
> instance Bifunctor Either where
>     bimap :: (a -> c) -> (b -> d) -> Either a b -> Either c d
>     bimap g h (Left a) = Left (g a)
>     bimap g h (Right b) = Right (h b)
 
And here we go: 
 
> newtype Curry f a b = Curry (f (a, b))
>     
> instance (CFunctor f ((->) :**: (->)) (->)) =>  Bifunctor (Curry f) where
>     bimap ac bd (Curry fp) = Curry $ cmap (ac :**: bd) fp 

__TODOs__
TODO think about that `id` issue.   
TODO Implement ProFunctor as CFunctor ((<-) :**: (->)) (->)
  


 

|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch08b_BiFunctorComposition

Notes about CTFP Part 1 Chapter 8. BiFunctor composition as Functor composition
===============================================================================
It is conceptually easier to think of bifunctor as simply a functor from a product category. 
This note uses this approach for composition leading to concepts of Functor product
and coproduct.

__Work in progress__

> {-# LANGUAGE TypeOperators #-}
> module CTNotes.P1Ch08b_BiFunctorComposition where
> import CTNotes.P1Ch08a_BiFunctorAsFunctor (Bifunctor, bimap)

Directly from the book

> newtype BiComp bf fu gu a b = BiComp (bf (fu a) (gu b))
> 
> instance (Bifunctor bf, Functor fu, Functor gu) =>
>   Bifunctor (BiComp bf fu gu) where
>     bimap f1 f2 (BiComp x) = BiComp ((bimap (fmap f1) (fmap f2)) x)

`Comp2` is a convenient type that subsumes binary operators on functors such as 
`Data.Functor.Product` and `Data.Functor.Sum` in the base package.
`Comp2` is a nominally typed version of (equivalent to):
```
type Comp2 bf fu gu a = BiComp bf fu gu a a
```

> newtype Comp2 bf fu gu a = Comp2 { runComp2 :: bf (fu a) (gu a) }
>
> instance (Bifunctor bf, Functor fu, Functor gu) => Functor (Comp2 bf fu gu) where
>   fmap f (Comp2 x) = Comp2 ((bimap (fmap f) (fmap f)) x)
>
> type Product f g a = Comp2 (,) f g a
> type Sum f g a = Comp2 Either f g a
> type (f :*: g) a  = Product f g a 
> type (f :+: g) a  = Sum f g a 

I need these in other notes.

this diagram illustrates what happens
```            
          Δ                   fu, gu                  bf
Hask   ----->   Hask x Hask  -------->  Hask x Hask ----->  Hask 
 a                a x a               (fu a) x (gu a)       bf (fu a) (gu a)
```

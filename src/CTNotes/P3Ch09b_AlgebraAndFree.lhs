|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch09a_Talg

__Very much work-in-progress__  
Various side notes about F-algerbas T-algerbars and the Free monad.

> module CTNotes.P3Ch09b_AlgebraAndFree where
> import Control.Monad

Ref: [Doel, schoolofhaskell](https://www.schoolofhaskell.com/user/dolio/many-roads-to-free-monads).  
Ref: [nlab free monad](https://ncatlab.org/nlab/show/free+monad)

Free-forgetful adjunction and monad algebra 
-------------------------------------------

In free-forgetful adjunction F -| U : C -> D involving categories of algebraic structures, 
the category of monad algebra of the functor UF (Monad side) is equivalent to the category C.
For example, monad algebra (T-algebra) on List functor has equivalent Monoid structure.

F-algebra vs T-algebra
----------------------
They can be very different, for example F-algebra for List does not have Monoid structure.

Note: the initial algebra of the list functor is isomorphic to:  

> data RoseTree = Node [RoseTree]

Free Monad 
---------- 
There is category Mnd where objects are monads and morphisms are natural transformations 
that play nice with monad structure. This category can also be viewed as category of monoids in 
monoidal category of endofunctors with composition.  Endo is std category of endofunctors.

Forgetful functor:
```
U :: Mnd -> Endo
U (T, join, return) = T
```
Free functor:

> data Free f a = Pure a | MkFree (f (Free f a))
> 
> instance Functor f => Functor (Free f) where
>   fmap fn (Pure a) = Pure (fn a)
>   fmap fn (MkFree expr) = MkFree (fmap fn <$> expr)
> instance Functor f => Monad (Free f) where
>   return = Pure
>   Pure x >>= g = g x
>   MkFree f >>= g = MkFree $ (>>= g) <$> f
> instance Functor f => Applicative (Free f) where
>   pure  = return
>   (<*>) = ap

_Side note:_ "The dual of substitution is redecoration" (Refs https://www.ioc.ee/~tarmo/papers/sfp01-book.pdf, 
http://comonad.com/reader/2011/free-monads-for-less/).  Think about fmap as substitution and join as renormalization. 
```
m >>= f = join (fmap f m)
```
In free join is not renormalizing

> joinF :: Functor f => Free f (Free f a) -> Free f a
> joinF (Pure a) = a
> joinF (MkFree as) = MkFree (fmap join as)

"free monad is purely defined in terms of substitution".  _End side note_.

The adjunction says that monad morphisms from `Free F A` to some other monad `M` correspond to 
natural transformations from `F` to `M`.  Natural transformations are used in implementing 
interpreters for Free DSLs, besides a nice theoretical backing for that approach is there something
deeper here? (TODO)  


Free Monad adjunction and F-algebras
------------------------------------
```
U:: F-Alg -> Hask
U (f, a, ev) = a  
 
F:: Hask -> F-Alg
F a = (f, Free f a, MkFree)

Hom ((f, Free f a, MkFree), (f, b, evb) =  a -> b
```
Each function a -> b has a corresponding F-alg morphism from Free f a to b.
This is done by using  `evb` to collapse all layers in Free f.

Tear down method

> type FAlgebra f a = f a -> a
> 
> iter :: Functor f => (f a -> a) -> Free f a -> a
> iter _ (Pure a) = a
> iter phi (MkFree m) = phi (iter phi <$> m)

This method is the essential part of natural transformation in the reverse direction

> nat1 :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
> nat1 a2b evb freefa = iter evb (fmap a2b freefa)

the other direction

> nat0 :: (Free f a -> b) -> a -> b
> nat0 f = f . Pure

Another reference: http://comonad.com/reader/2011/free-monads-for-less/

|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch08b_FalgFreeMonad

Notes about CTFP Part 3 Chapter 8. F-Algebras. Free
===================================================

Notes about F-algerbas and the free monad.
The book does not talk about Free but I decided to research it and I wrote this note about it. 

Book Ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)
[P3 Ch8. F-Algebras](https://bartoszmilewski.com/2017/02/28/f-algebras/).

Refs: [Doel, schoolofhaskell](https://www.schoolofhaskell.com/user/dolio/many-roads-to-free-monads)  
  [comonad reader](http://comonad.com/reader/2011/free-monads-for-less/)  
  [nlab free monad](https://ncatlab.org/nlab/show/free+monad)  


> module CTNotes.P3Ch08b_FalgFreeMonad where
> import Control.Monad


Free Monad
----------
Free functor (free monad):

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


There is category _Mnd_ where objects are monads and morphisms are natural transformations 
that play nice with the monadic structure. This category can also be viewed as category of monoids in 
monoidal category of endofunctors with composition.  
_Endo_ is standard category of endofunctors.
(See [nlab free monad](https://ncatlab.org/nlab/show/free+monad) for more information.)

Forgetful functor:
```
U :: Mnd -> Endo
U (T, join, return) = T
```
Free functor
```
F :: Endo -> Mnd
F (Fx) = Free Fx 
```
form an adjunction F -| U.

The adjunction says that monad morphisms (in _Mnd_) from `Free F A` to some other monad `M` correspond to 
natural transformations from `F` to `M`.  Natural transformations are used in implementing 
interpreters for Free DSLs. TODO Is this a theoretical backing for that DSL approach?


__Side note:__ As pointed out by the above [comonad post](http://comonad.com/reader/2011/free-monads-for-less/)  
__"The dual of substitution is redecoration"__    
(see also https://www.ioc.ee/~tarmo/papers/sfp01-book.pdf).
  
Think about fmap as substitution and join as renormalization. 
```
m >>= f = join (fmap f m)
```
In `Free` join is not renormalizing!

> joinF :: Functor f => Free f (Free f a) -> Free f a
> joinF (Pure a) = a
> joinF (MkFree as) = MkFree (fmap joinF as)

"free monad is purely defined in terms of substitution".  
_End side note_.



Free Monad Adjunction and F-algebras
------------------------------------
For a fixed functor `f`, in pseudo-Haskell:
```
U:: F-Alg -> Hask
U (f, a, ev) = a  
 
F:: Hask -> F-Alg
F a = (f, Free f a, MkFree)

Hom ((f, Free f a, MkFree), (f, b, evb) ~=  a -> b
```

This adjunction viewed as isomorphism of homsets means that
each function `a -> b` has a corresponding F-alg morphism from `Free f a` to `b`.
This is done by using  `evb` to collapse all layers in Free f.

> type FAlgebra f a = f a -> a

Following method is the essential part of isomorphism in the reverse direction

> iter :: Functor f => (f a -> a) -> Free f a -> a
> iter _ (Pure a) = a
> iter phi (MkFree m) = phi (iter phi <$> m)

> iso1 :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
> iso1 a2b evb freefa = iter evb (fmap a2b freefa)
>
> iso0 :: (Free f a -> b) -> a -> b
> iso0 f = f . Pure

__More about Free__  
The comonad post linked above continues as a 3 part sequel, [N_P3Ch11a_KanExt](N_P3Ch11a_KanExt) has all of these posts linked.

Cofree
------
This section is mostly a TODO.
Documentation in `free` package has good short description of Cofree.   
https://hackage.haskell.org/package/free-5/docs/Control-Comonad-Cofree.html

Cofree and Free work together well.
I have used it in my GraphPlay project. 
(TODO find good writeup)  
See http://blog.sigfpe.com/2014/05/cofree-meets-free.html

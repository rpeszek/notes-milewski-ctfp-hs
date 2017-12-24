|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch06a_CTMonads

__Work in progress__  

Notes related to CTFP Part 3 Chapter 6.  Monads 
===============================================
This is bunch of loose notes about things like Monad composability, distribution laws, etc.


> {-# LANGUAGE InstanceSigs, TypeOperators, MultiParamTypeClasses, ScopedTypeVariables, FlexibleInstances #-}
>
> module CTNotes.P3Ch06a_CTMonads where
> import Control.Monad 
> import Data.Functor.Compose (Compose(..))
> import CTNotes.P1Ch07_Functors_Composition ((:.))

Monad Laws in terms of return/join definition
---------------------------------------------

Eta/return viewed as Identity :~> m, naturality condition: 
```
return . f ≡ fmap f . return
```
Mu/join viewed as m :.: m :~> m, naturality condition: 

```
join . fmap (fmap f) ≡ fmap f . join
```

Laws:
```
join . fmap join     ≡ join . join
join . fmap return   ≡ join . return ≡ id
```

Loose Notes (Products, distribution laws) 
-----------------------------------

Monads are closed with respect to functor product
```
(Monad f, Monad g) => Monad (Product f g)
```

We have convenient ways to distribute over traversables
```
sequence :: (Traversable t, Monad m) => t (m a) -> m (t a)
```
or (same foldr idea) over simple products

> dist3 :: Monad m =>  (m a, m b, m c) -> m (a, b, c)
> dist3 (ma, mb, mc) = do
>      a <- ma
>      b <- mb
>      c <- mc
>      return (a, b, c)

Functor composition is crucial in CT definition of Monad but composition of monads is not always a monad.
I found a paper about Monad composition: [Jones, Duponcheel](http://web.cecs.pdx.edu/~mpj/pubs/RR-1004.pdf).
It shows several approaches to composing monads.

I have played with composing monads using what is called distribution law.
Paper calls is swap construction, I based it on this [wikipedia](https://en.wikipedia.org/wiki/Distributive_law_between_monads) 

It turns out that there is a natural monad structure on the composite functor m :. n 
if monad m distributes over the monad n (if there is a _Natural Transformation_ `forall a . (n :. m) a -> (m :. n) a`
that satisfies certain conditions).  

> class (Monad n, Monad m) => Dist m n where
>    dist :: n (m a) -> m (n a)

Certain distribution laws (see below) need to be satisfied, otherwise composition will fail to satisfy monad laws.

> joinComp :: forall n m a. Dist m n => m ( n ( m (n a))) -> m (n a)
> joinComp = (join . (fmap . fmap) join) . (fmap dist)
> 
> returnComp :: Dist m n => a -> m (n a)
> returnComp =  return . return
>
> fmapComp :: Dist m n => (a -> b) -> m (n a) -> m (n b)
> fmapComp = fmap . fmap 
>
> instance Dist m n => Monad (Compose m n) where
>    return  = Compose . returnComp  
>    Compose mna >>= f = Compose $ joinComp (fmapComp (getCompose . f) mna)


__Distribution Laws__ (again following [Wikipedia article](https://en.wikipedia.org/wiki/Distributive_law_between_monads)):
```
joinM . fmapM dist . dist ≡ dist . fmapN joinM  (n (m (m a)) -> m (n a))
fmapM joinN . dist . fmapN dist ≡ dist . joinN  (n (n (m a)) -> m (n a))
dist . fmapN returnM ≡ returnM                  (n a -> m (n a))
dist . returnN ≡ fmapM returnN                  (m a -> m (n a))
```

In Haskell:

> diag1a :: Dist m n => n (m (m a)) -> m (n a)
> diag1a = join . fmap dist . dist
> diag1b :: Dist m n => n (m (m a)) -> m (n a)
> diag1b = dist . fmap join 
>
> diag2a :: Dist m n => n (n ( m a)) -> m (n a)
> diag2a =  fmap join . dist . fmap dist
> diag2b :: Dist m n => n (n ( m a)) -> m (n a)
> diag2b =  dist . join
>
> diag3a :: Dist m n => n a -> m (n a)
> diag3a =  dist . fmap return
> diag3b :: Dist m n => n a -> m (n a)
> diag3b = return
> 
> diag4a :: Dist m n => m a -> m (n a)
> diag4a = dist . return
> diag4b :: Dist m n => m a -> m (n a)
> diag4b = fmap return


It could be easier to just check monad laws:
```
joinComp . fmapComp joinComp     ≡ joinComp . joinComp
joinComp . fmapComp returnComp   ≡ joinComp . returnComp ≡ id
```

TODO __Writer Example__:

Writer monad (taken from the paper)

> instance (Monoid s, Monad m) => Dist m ((,) s) where
>    dist (s, m) = do 
>             a <- m
>             return (s, a)

satisfies needed laws. 

TODO __List Example__:    

`sequence` can be used to implement Dist, but the required laws are not always satisfied.
They ARE satisfied, however, with additional assumption

> class Monad m => CommutativeMonad m 
>
> instance CommutativeMonad m => Dist m [] where
>     dist = sequence

Monad m is commutative if expression 
```
do 
   x <- a
   y <- b
   f x y

-- is equivalent to 
do 
   y <- b
   x <- a
   f x y
```
(If order of effects does not matter, things can be done concurrently.) 
(Reader has it, State does not, some monads have it if we exclude `_|_`).
[see also this](https://github.com/basvandijk/monad-control/issues/28)


TODO Other composition approaches from the paper
TODO Monad composability relations to transformers

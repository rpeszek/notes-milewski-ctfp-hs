TODO work in progress

> {-# LANGUAGE TypeOperators #-}

> module CTNotes.P1Ch07_Functors where

> newtype FCompose f g a = FCompose { getFComp :: f (g a) }
> instance (Functor f, Functor g) => Functor (FCompose f g) where
>    fmap f (FCompose x) = FCompose (fmap (fmap f) x)

> type f :. g = FCompose f g

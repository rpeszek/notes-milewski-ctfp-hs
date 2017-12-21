|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch06a_CTMonads

__Work in progress__  

> module CTNotes.P3Ch06a_CTMonads where
> import Control.Monad 

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

Loose Notes:   
Monads preserve product 
```
(Monad f, Monad g) => Monad (Product f g)
```
However, composition of monads is not always a monad ([N_P1Ch07_Functors_Composition](N_P1Ch07_Functors_Composition)).

We have ways to distribute over a monad
```
sequence :: (Traversable t, Monad m) => t (m a) -> m (t a)
```
or something trivial like this

> dist :: Monad m =>  (m a, m b, m c) -> m (a, b, c)
> dist (ma, mb, mc) = do
>      a <- ma
>      b <- mb
>      c <- mc
>      return (a, b, c)

TODO distributive law between monads

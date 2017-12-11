|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch06a_CTMonads

__Work in progress__  

> module CTNotes.P3Ch06a_CTMonads where

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

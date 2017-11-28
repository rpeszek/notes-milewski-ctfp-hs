|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch07b_Functors_AcrossCats

__ Work in progress __

Note about CTFP Part 1 Chapter 7. Functors on non-Hask categories 
==================================================================
Ref: https://hackage.haskell.org/package/category-extras-0.53.5/docs/Control-Functor-Categorical.html

Book ref:
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 7](https://bartoszmilewski.com/2015/01/20/functors/)

> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE DataKinds #-}
>
> module CTNotes.P1Ch07b_Functors_AcrossCats where
> import Data.Functor.Const (Const(..))
> import Control.Category 
> import Prelude(undefined, ($))
> import qualified CTNotes.P1Ch03b_FiniteCats as Finite


`category-extras` defines `CFunctor` (quoted code):
```
class (Category r, Category s) => CFunctor f r s | f r -> s, f s -> r where
  cmap :: r a b -> s (f a) (f b)
```

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

> test :: Const a (x :: Finite.Object) -> Const a (x :: Finite.Object)
> test = cmap Finite.MorphId

But this would not compile:

```
-- Bad code
test :: Const a (x :: Finite.Object) -> Const a (x :: Finite.Object)
test = cmap Finite.MorphAB
```
 
TODO: more examples?

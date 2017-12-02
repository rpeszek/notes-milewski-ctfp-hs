|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch05b_YonedaNonHask

__Work-in-progress__

Notes about CTFP Part 2 Chapter 5. Yoneda Lemma from non-Hask categories
========================================================================

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE Rank2Types #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module CTNotes.P2Ch05b_YonedaNonHask where
> import Control.Category 
> import Prelude(undefined, ($))
> import Data.Functor.Const (Const(..))
> import CTNotes.P1Ch07b_Functors_AcrossCats (CFunctor, cmap)

Generalized Yoneda Definition
-----------------------------
Quoted from `Control.Category` with explict kind signature:
```
class Category (homset:: k -> k -> *) where
     id :: homset a a
     (.) :: homset b c -> homset a b -> homset a c
```
Notice that these `homset` with custom kinds but live in Hask (`*`).
That corresponds to 'C(a,b)' being in __Set__. 
 
This generalized definition keeps kinds explicit  
TODO Natural Transformations probably need more information  
TODO Quite sure that Naturality Conditions no longer automatic  

> newtype CYoneda (homset :: k -> k -> *) (f :: k -> *) a = CYoneda { runCYoneda :: forall x. (homset a x -> f x) } 

because of kind signature `x` is inferred as `x :: k`.


Functor Instance
----------------
Quoted from [N_P1Ch07b_Functors_AcrossCats](N_P1Ch07b_Functors_AcrossCats):
```
class (Category homset, Category s) => CFunctor f homset s  where
   cmap :: homset a b -> s (f a) (f b)
```

Generalized CYoneda still is automatically a functor

> instance (Category homset) => CFunctor (CYoneda homset f) homset (->) where
>    cmap f y = CYoneda (\k -> (runCYoneda y) (k . f))

Note `(k . f)` happens in the `homset` category


Isomorphism
-----------
TODO


CoYoneda 
--------
TODO


Examples
--------
TODO

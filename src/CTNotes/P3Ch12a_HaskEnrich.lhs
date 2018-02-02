|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch12a_HaskEnrich

A very short note about viewing Haskell in the context of an enriched category.  
Book Ref: [Part 3 Chapter 12, enhanced categories](https://bartoszmilewski.com/2017/05/13/enriched-categories)

> {-# LANGUAGE PolyKinds #-}
> module CTNotes.P3Ch12a_HaskEnrich where
> import Prelude

In a nutshell, enriched categories are based on association C(a,b) of objects a and b in C, 
C does not need to have any categorical structure, 
C(a,b) is an object in some monoidal category V, and V is used to provide categorical 
structure for C.

Repeating definition from Control.Category

> class Category cat where
>    id :: cat a a
>    (.) :: cat b c -> cat a b -> cat a c
  
```
ghci>  :k Category
Category :: (k -> k -> *) -> Constraint
```  

Hask is a monoidal category with (,) as product and () (Unit) as Identity 
(see [N_P3Ch06c_MonoidalCats](N_P3Ch06c_MonoidalCats)). 
I can think of `*` (Hask) as V and `cat a b` as C(a,b) (note `cat :: k -> k -> *`).
This way any kind `k` can be enriched over Hask.

`PolyKinds` can be viewed as enriching kinds `k` over Hask!
  

|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch12a_HaskEnrich

> {-# LANGUAGE PolyKinds #-}
> module CTNotes.P3Ch12a_HaskEnrich where
> import Prelude (undefined)

Enriched categories are based on association C(a,b) of objects a and b in C, that is an object in some monoidal category V.

Following Control.Category

> class Category cat where
>    id :: cat a a
>    (.) :: cat b c -> cat a b -> cat a c
  
```
ghci>  :k Category

```  

Hask is a monoidal category with (,) as product and () (Unit) as Identity (see [N_P3Ch06c_MonoidalCats](N_P3Ch06c_MonoidalCats)). 
So if I think of `*` as Hask I can think of the instances of the above class as a categories enriched over Hask!
  

|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch15b_CatsAsMonads

"So, all told, a category is just a monad in the bicategory of spans."  
This note traces that statement using simple category `A->B=>C` from [N_P1Ch03b_FiniteCats (FC)](N_P1Ch03b_FiniteCats)
and Haskell.

> {-# LANGUAGE DataKinds 
>  , KindSignatures 
>  , GADTs 
>  #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module CTNotes.P3Ch15b_CatsAsMonads where
> import qualified CTNotes.P1Ch03b_FiniteCats as FC
> import CTNotes.P1Ch03b_FiniteCats (Object(..))
> import CTNotes.P3Ch15a_Spans
> import Data.Proxy


Consider the category `A->B=>C` from [N_P1Ch03b_FiniteCats (FC)](N_P1Ch03b_FiniteCats) redefined here to follow 
the notation from the book:

> type Ob = FC.Object

(Equivalently FC.ObjectRep could been used instead.)

Type `Ar` is isomorphic to `FC.HS` (to be precise, to the flattened version `HomSetFlat` shown below) 
and marks domains and codomains using data constructors

> data Cod (a :: FC.Object) = CodA (FC.HS a 'A) | CodB (FC.HS a 'B) | CodC (FC.HS a 'C)
>
> data Ar = DomA (Cod 'A) | DomB (Cod 'B) | DomC (Cod 'C)
>
> decCod :: Cod a -> Ob
> decCod (CodA _) = FC.A
> decCod (CodB _) = FC.B
> decCod (CodC _) = FC.C
> 
> dec :: Ar -> (Ob, Ob) 
> dec (DomA x) = (FC.A, decCod x)
> dec (DomB x) = (FC.B, decCod x) 
> dec (DomC x) = (FC.C, decCod x)
>
> dom :: Ar -> Ob 
> dom  = fst . dec
>
> cod :: Ar -> Ob
> cod  = snd . dec


The book defines the 1-cell span `Ob <- Ar -> Ob` (monad `T`) as something that I would like to express as
 
> t :: Cell1 Ar Ob Ob
> t = Cell1 dom cod

and the 1-cell `I` as the identity cell

> i :: Cell1 Ob Ob Ob
> i = Cell1 id id

For `t` to be a monad I need to define two 2-cells
```
η :: I -> T
μ :: T ∘ T -> T 
```
Translating this to the `data Cell2 x y a b = Cell2 (x -> y)` from [N_P3Ch15a_Spans](N_P3Ch15a_Spans)

```
η :: I -> T

       Ob
    /  |  \ 
   /id |η  \id
  /    |    \ 
 Ob <- Ar ->  Ob
```

> eta :: Cell2 Ob Ar Ob Ob
> eta = 
>    let pickId :: Ob -> Ar
>        pickId A = DomA (CodA (FC.MoId FC.ARep))
>        pickId B = DomB (CodB (FC.MoId FC.BRep))
>        pickId C = DomC (CodC (FC.MoId FC.CRep))
>    in  Cell2 pickId


2-cell `μ :: T ∘ T -> T` defines the composition and translates to
```
mu :: Pullback Ar Ar Ob -> Ar
```
Due to complexity of describing pullback in a programming language, [N_P3Ch15a_Spans](N_P3Ch15a_Spans) 
has used existential type 
```
data Pullback x y a = forall z . Pullback z (z -> x) (z -> y)
``` 
that is not trivial to work with.  
However, for this simple example, I can just define pullback explicitly.
That type should consist of composable pairs of 1-cells.

> data PullbackForAr where
>    OnA :: FC.HS 'A 'A -> FC.HS 'A a -> PullbackForAr
>    OnB :: FC.HS  a 'B -> FC.HS 'B c -> PullbackForAr
>    OnC :: FC.HS  a 'C -> FC.HS 'C 'C -> PullbackForAr

`mu :: PullbackForAr -> Ar` can be defined by repeating the definition of `FC.comp`.  
However, I can do better and use GHC to check that `mu` is just the composition 
in disguise:

> data HomSetFlat where
>   HsFlat :: (FC.HS a b) -> HomSetFlat
>
> mu :: PullbackForAr -> Ar
> mu (OnA m1 m2) = iso . HsFlat $ m2 `FC.comp` m1
> mu (OnB m1 m2) = iso . HsFlat $ m2 `FC.comp` m1
> mu (OnC m1 m2) = iso . HsFlat $ m2 `FC.comp` m1

and the tedious part is the definition of `iso`

> iso :: HomSetFlat -> Ar
> iso (HsFlat (FC.MoId FC.ARep)) = DomA (CodA (FC.MoId FC.ARep))
> iso (HsFlat (FC.MoId FC.BRep)) = DomB (CodB (FC.MoId FC.BRep))
> iso (HsFlat (FC.MoId FC.CRep)) = DomC (CodC (FC.MoId FC.CRep))
> iso (HsFlat FC.MoAB) = DomA (CodB FC.MoAB)
> iso (HsFlat FC.MoBC1) = DomB (CodC FC.MoBC1)
> iso (HsFlat FC.MoBC2) = DomB (CodC FC.MoBC2)
> iso (HsFlat FC.MoAC1) = DomA (CodC FC.MoAC1)
> iso (HsFlat FC.MoAC2) = DomA (CodC FC.MoAC2)

"So, all told, a category is just a monad in the bicategory of spans." in Haskell!

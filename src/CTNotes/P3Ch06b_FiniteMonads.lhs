|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch06b_FiniteMonads

Notes related to CTFP Part 3 Chapter 6. Monads on finite categories
===================================================================

__Work in progress, this topic needs more research__  
 
I am interested in modeling finite categories in Haskell, but I still do not know a lot about it. 
This note includes general thoughts about monads in a finite category and focuses on category `A->B=>C` introduced in 
[N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats).

This note is only loosely related to the book
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch. 6 Monads Categorically](https://bartoszmilewski.com/2016/12/27/monads-categorically/)


> {-# LANGUAGE DataKinds 
>  , KindSignatures 
>  , FlexibleInstances
>  , TypeFamilies 
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

> module CTNotes.P3Ch06b_FiniteMonads where
> import CTNotes.P1Ch03b_FiniteCats


It is about having enough arrows
--------------------------------
Parametricity is lost in finite categories (see [N_P1Ch10b_NTsNonHask](N_P1Ch10b_NTsNonHask)).
However, some laws can be automatically satisfied for other reasons. 
For example, if finite category has very few morphisms (for example when is thin), then the naturality 
```
               fmap_F f     
          F a  --------> F b
           |             |
      nt   |             |  nt
           |             |  
          \ /           \ /
          G a  -------> G b
               fmap_G f  
                  
   fmap_G f . alpha_a ≡ alpha_b . fmap_F f
```
is automatic (because there at most one possible morphism F a -> G b).  
That is, if there are enough many arrows to define that diagram (if functors and natural transformations are defined)
then the naturality condition has to hold.  
Thus, the most interesting question for finite categories seems to be if there are enough many arrows.

Monads
------
To talk about a monad I need endofunctor F and 2 natural transformations `eta :: Id -> F` and `mu :: F ∘ F -> F`.
Both functors and natural transformations on `A->B=>C` do not have any point-wise aspect and 
are just mappings of objects A,B,C and enumerated morphisms.   
When restricted to objects, eta becomes equivalent to the functor itself.

__Monad Example__
Consider following endofunctor 
```
     A ->B => C
      \  |    |
F      \ |    |
        \ /  \ /
     A   B => C
``` 
F collapses A -> B into B and is identity on both morphisms B => C.
Eta and mu need to be defined on the image of F only and both can be defined by selecting identity morphisms.  
The monad laws (both required on the image of F which is B => C):
```
join . fmap join     ≡ join . join         -- on the image of functor
join . fmap return   ≡ join . return ≡ id  -- on the image of functor
```
are trivially satisfied (join=mu, return=eta). F is a monad.
 
Haskell code representing F could look like 
(strictly interpreting action on Objects to have kind signature `F :: Object -> Object)`:

> type family F (a :: Object) :: Object where
>   F 'A = 'B 
>   F 'B = 'B 
>   F 'C = 'C
>
> class FmapF (a:: Object) where
>    fmap_F :: HomSet a b -> HomSet (F a) (F b)
> 
> instance FmapF 'A where
>    fmap_F MorphId = MorphId :: HomSet 'B 'B
>    fmap_F MorphAB = MorphId :: HomSet 'B 'B
>    fmap_F MorphAC1 = MorphBC1
>    fmap_F MorphAC2 = MorphBC2
> instance FmapF 'B where
>    fmap_F MorphId  = MorphId
>    fmap_F MorphBC1  = MorphBC1
>    fmap_F MorphBC2  = MorphBC2
> instance FmapF 'C where
>    fmap_F MorphId  = MorphId
>
> type family Mu (a:: Object) :: Object where
>   Mu 'B = 'B 
>   Mu 'C = 'C
>
> type family Eta (a:: Object) :: Object where
>   Eta 'B = 'B 
>   Eta 'C = 'C

but I am sure that there is a better code representation of F.


__Non-monad example__
```
     A ->B => C
      \    \  |
G      \    \ |
        \ /  \ /
     A   B -> C
``` 
G shifts forward A to B, B to C, it picks first morphism MorphBC1 as image of MorphAB and it collapses morphisms B => C    
The problem is that there is no way to implement `join` because category does not have arrows `C -> B`.

```
     A    C   
      \    
G∘G    \   
        \ /  
     A   C   

            fmap_GG MorphAB = 
            MorphId :: HomSet C C
    G∘G A = C  -------> G∘G B = C
           ?                |
      nt   ?                |   
           ?                |  
          \ /              \ /
       G A = B  --------> G B = C
             fmap_G MorphAB =
               MorphBC1
```

> type family G (a :: Object) :: Object where
>   G 'A = 'B 
>   G 'B = 'C 
>   G 'C = 'C
>
> class FmapG (a:: Object) where
>    fmap_G :: HomSet a b -> HomSet (G a) (G b)
>
> instance FmapG 'A where
>    fmap_G MorphId = MorphId :: HomSet 'B 'B
>    fmap_G MorphAB = MorphBC1 
>    fmap_G MorphAC1 = MorphBC1
>    fmap_G MorphAC2 = MorphBC1
> instance FmapG 'B where
>    fmap_G MorphId  = MorphId
>    fmap_G MorphBC1  = MorphId
>    fmap_G MorphBC2  = MorphId
> instance FmapG 'C where
>    fmap_G MorphId  = MorphId

These 2 simple examples aside, this topic needs more research

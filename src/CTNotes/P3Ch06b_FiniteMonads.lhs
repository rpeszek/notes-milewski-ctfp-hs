|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch06b_FiniteMonads

__Work in progress__   
This note is sure to change when I understand more.  
It includes general thoughts about finite category monads and focuses on category `A->B=>C` introduced in N_P1Ch03b_FiniteCats

> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

> module CTNotes.P3Ch06b_FiniteMonads where
> import CTNotes.P1Ch03b_FiniteCats


Finite categories lose parametricity and free theorems N_P1Ch10b_NTsNonHask.
However, some automatic goodness seems to come back when examining endofunctors. 
For example, if finite category has very few morphisms (maybe it is thin), then the naturality 
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
This is as long as there are enough many arrows to define that diagram (if functors and nt-ies are defined).

The most interesting question seems to be if there are enough many arrows.

Since there is no point-wise aspect, eta becomes simply equivalent to the functor itself (as a function acting on objects).

__Monad Example__
Consider these 2 endofunctors on `A->B=>C`
```
     A ->B => C
      \  |    |
F      \ |    |
        \ /  \ /
     A   B => C
``` 
F collapses A -> B into B and is identity on B => C.
By construction join (mu) F is identity and return (eta) F is also identity on B => C.
Thus, monad laws (both required on the image of F which is B => C)
```
join . fmap join     ≡ join . join         -- on the image of functor
join . fmap return   ≡ join . return ≡ id  -- on the image of functor
```
are trivially satisfied.  F is a monad.
  
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

(Eta and F are the same)


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

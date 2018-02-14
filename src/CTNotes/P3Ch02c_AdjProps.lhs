|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch02c_AdjProps

Notes about CTFP Part 3 Chapter 2. Adjunction properties 
========================================================

Loose notes about some programming properties of adjunctions. 

Book Ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
          [Part 3. Ch.2 Adjunctions](https://bartoszmilewski.com/2016/04/18/adjunctions/)


> {-# LANGUAGE  MultiParamTypeClasses
>  , FlexibleInstances 
>  #-}
>
> module CTNotes.P3Ch02c_AdjProps where
> import CTNotes.P3Ch02a_CurryAdj
> import Data.Functor.Compose (Compose(..))
> import CTNotes.P1Ch08b_BiFunctorComposition


Composition
-----------
```
            l2              l1
        <---------      <---------   
      |              |             |
      |              |             | 
      |              |             |  
     \ /            \ /           \ /
         --------->     --------->  
            r2             r1
```
Drawing the above picture explains this code:

> instance (Adjunction l1 r1, Adjunction l2 r2) =>
>         Adjunction (Compose l2 l1) (Compose r1 r2) where
>    unit   = Compose . leftAdjunct (leftAdjunct Compose)
>    counit = rightAdjunct (rightAdjunct getCompose) . getCompose


Sum/Product Law
---------------
Functor product and coproduct defined in [N_P1Ch08b_BiFunctorComposition](P1Ch08b_BiFunctorComposition)
```
newtype Comp2 bf fu gu a = Comp2 (bf (fu a) (gu a))

type Product f g x    ~= Comp2 (,) f g x
type Coproduct f g x  ~= Comp2 Either f g x
``` 

> instance (Adjunction l1 r1, Adjunction l2 r2) =>
>          Adjunction (Comp2 Either l1 l2) (Comp2 (,) r1 r2) where
>    unit a =  Comp2 (leftAdjunct (Comp2 . Left) a, leftAdjunct (Comp2 . Right) a)
>    counit (Comp2 (Left l)) = rightAdjunct (fst . runComp2) l      
>    counit (Comp2 (Right r)) = rightAdjunct (snd . runComp2) r

```
                                            (C x C)(Δ c,<a, b>) 
                                                   ~= C(c, a*b)

                Either          l1, l2           Δ
             <-----=====      <========     <====-----   
           |              ||             ||             |
           |              ||             ||             | 
           |              ||             ||             |  
          \ /            \  /           \  /           \ /
              ------====>     ========>     =====---->  
                   Δ           r1, r2           (,)

    C(a+b, c) ~= 
    (C x C)(<a, b>, Δ c)
```
Again, drawing a picture explains the code!


Free-Forgetful, Free Monad Adjunction
--------------------------------------
See the end of [N_P3Ch08a_Falg](N_P3Ch09a_Talg) note about relationship between 
free-forgetful adjunctions and algebras.
 

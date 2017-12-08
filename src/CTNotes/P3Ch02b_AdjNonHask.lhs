|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch02b_AdjNonHask

Notes about CTFP Part 3 Chapter 2. Product as adjunction, non-Hask generalizations 
==================================================================================

Book Ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
          [Part 3. Ch.2 Adjunctions](https://bartoszmilewski.com/2016/04/18/adjunctions/)

> {-# LANGUAGE  MultiParamTypeClasses
>   , InstanceSigs
>   , ScopedTypeVariables
>   , FunctionalDependencies
>   , FlexibleContexts
>   , FlexibleInstances 
>   #-}
> 
> module CTNotes.P3Ch02b_AdjNonHask where
> import qualified CTNotes.P3Ch02a_CurryAdj as AdjHask
> import CTNotes.P1Ch08a_BiFunctorAsFunctor
> import Data.Functor.Identity
> import Prelude hiding ((.), id)
> import Control.Category (Category, (.), id)


Adjunction generalized to non-Hask categories
---------------------------------------------
 
General Functor instance follows [category-extras](https://hackage.haskell.org/package/category-extras-0.53.5).  
I am redefining it to add back functional dependencies.
(avoided before to simplify things and to solve problems with `Const` functor, 
this definition matches `category-extras`),
  
> class (Category r, Category s) => CtFunctor f r s | f r -> s, f s -> r where
>     cmap :: r a b -> s (f a) (f b)
  
Using [Ch.2](https://bartoszmilewski.com/2016/04/18/adjunctions/)
naming conventions (using `catc` for category __C__ hom-set and `catd` for category __D__) 
```
          catc           catd
                   l     
          l d <-------   d
           |             |
   counit  |             | unit
           |             |  
          \ /           \ /
           c  ------->  r c
                  r  
```

> class (CtFunctor l catd catc, CtFunctor r catc catd) => CtAdjunction l r catc catd  where 
>     unit   :: catd d (r (l d))
>     counit :: catc (l (r c)) c
>     leftAdjunct  :: catc (l d) c -> catd d (r c)
>     rightAdjunct :: catd d (r c) -> catc (l d) c
> 
>     unit = leftAdjunct id
>     counit = rightAdjunct id
>     leftAdjunct f = cmap f . unit
>     rightAdjunct f = counit . cmap f
  
Proof that this is generalization or Hask endofunctor adjunctions
  
> instance (CtFunctor l (->) (->), CtFunctor r (->) (->), AdjHask.Adjunction l r) => CtAdjunction l r (->) (->) where
>    unit = AdjHask.unit
>    counit = AdjHask.counit
     

Adjunction between functor and bifunctor      
----------------------------------------     
Since there are problems in defining `id` and creating instance of `Control.Category` for product __Hask x Hask__ (`(->) :**: (->)`),
this section defines adjunction between bifunctor and functor (__C = Hask x Hask__, __D = Hask__).    
```
 Hask x Hask            Hask
               l1, l2    
(l1 d) (l2 d) <-------   d
  |        |             |
  | counit |             | unit
  |        |             |  
 \ /      \ /           \ /
 c1       c2  ------->  r c
                  r  
```
     
> class (Bifunctor r, Functor l1, Functor l2)  => Ct21Adjunction l1 l2 r | r -> l1, r -> l2, l1 l2 -> r where
>     unit21 :: d -> r (l1 d) (l2 d)
>     counit21_1 :: l1 (r c1 c2) -> c1  -- 2 morphism in Hask x Hask representing counit21 component
>     counit21_2 :: l2 (r c1 c2) -> c2
>     leftAdjunct21 :: (l1 d -> c1) -> (l2 d -> c2) -> d -> r c1 c2
>     rightAdjunct21 :: (d -> r c1 c2) -> (l1 d -> c1, l2 d -> c2)
>     
>     unit21 = leftAdjunct21 id id
>     counit21_1 = fst $ rightAdjunct21 id
>     counit21_2 = snd $ rightAdjunct21 id
>     leftAdjunct21 f1 f2 = bimap f1 f2 . unit21
>     rightAdjunct21 f = (counit21_1 . fmap f, counit21_2 . fmap f) 
       
Product as adjunction
---------------------
```
 Hask x Hask            Hask
         Identity, Identity    
  d        d  <-------   d
  |        |             |
  | counit |             | unit
  |        |             |  
 \ /      \ /           \ /
 c1       c2  -------> (c1, c2)
                  (,)  
```

> instance Bifunctor (,) where
>     bimap :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
>     bimap g h (a,b) = (g a, h b)
>  
> instance Ct21Adjunction Identity Identity (,) where
>     leftAdjunct21 :: (Identity d -> c1) -> (Identity d -> c2) -> d -> (c1, c2)
>     leftAdjunct21 dc1 dc2 d = ((dc1 . Identity) d, (dc2 . Identity) d) 
>      
>     rightAdjunct21 :: (d -> (c1, c2)) -> (Identity d -> c1, Identity d -> c2)
>     rightAdjunct21 dc1c2 = (fst . dc1c2 . runIdentity, snd . dc1c2 . runIdentity)

I used `21` to indicate product category __Hask x Hask__ on the left and __Hask__ 
on the right.
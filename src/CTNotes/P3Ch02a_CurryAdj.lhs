|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch02a_CurryAdj

Notes about CTFP Part 3 Chapter 2.  Exponential from Adjunction 
===============================================================
Currying yields exponential adjunction, `State`/`Store` construction.

Book Ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
          [Part 3. Ch.2 Adjunctions](https://bartoszmilewski.com/2016/04/18/adjunctions/)

> {-# LANGUAGE  MultiParamTypeClasses, InstanceSigs #-}
>
> module CTNotes.P3Ch02a_CurryAdj where
> import Data.Tuple (curry, uncurry, swap)

Adjunction definition from the book with functional dependencies and representable constraint removed, 
to keep it focused

> class (Functor l, Functor r) => Adjunction l r  where
>     unit   :: d -> r (l d)
>     counit :: l (r c) -> c
>     leftAdjunct  :: (l d -> c) -> d -> r c
>     rightAdjunct :: (d -> r c) -> l d -> c
> 
>     unit = leftAdjunct id
>     counit = rightAdjunct id
>     leftAdjunct f = fmap f . unit
>     rightAdjunct f = counit . fmap f

Implementation emphasizes that  
  `(-, a) ⊣ a -> -`    
is all about currying.   
These diagrams use notations from the book
```
                 L
      (z, a) <------   z
         |             |
 counit  |             | unit
        \ /           \ /
         b  ------->  a -> b
                R
               
                L
                --- d    
              /     |
            \/      |
       (d,a)        | unit = x -> a -> (x, a)
            /\      |
              \    \ /
                --- a -> (d,a)
                R
 
      (a->c,a) --
                  \
                   \/
                     a -> c
                   /\
                  /
            c  --    
```                
In the instance implementation I need to have (z, a) flipped to (a,z)                

> instance Adjunction ((,) a) ((->) a) where
>     unit :: d -> a -> (a, d)
>     unit = flip (,)    -- x a = (a,x) 
>     counit :: (a, a -> c) -> c
>     counit (x, ca) = ca x
>     leftAdjunct :: ((a, z) -> b) -> z -> a -> b
>     leftAdjunct azb = curry $ azb . swap      -- or zab a z  = zab (z,a)
>     rightAdjunct :: (z -> a -> b) -> (a, z) -> b
>     rightAdjunct zab = uncurry $ flip zab     -- or zab ~(z,a) = zab a z
 
Notice the need to use ugly `flip` and `swap` caused by using (a,-) and not (-,a) as the book does!

TODO: what are programming implication of this adjunction for non-Hask categories? 

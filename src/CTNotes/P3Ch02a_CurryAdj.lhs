|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch02a_CurryAdj

Notes about CTFP Part 3 Chapter 2.  Adjunctions. Exponential from Adjunction 
============================================================================
Currying yields exponential adjunction, `State`/`Store` construction.
This note adds some Haskell code that follows the "Exponential from Adjunction" 
section in the book. 

Book Ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
          [Part 3. Ch.2 Adjunctions](https://bartoszmilewski.com/2016/04/18/adjunctions/)

> {-# LANGUAGE  MultiParamTypeClasses, InstanceSigs #-}
>
> module CTNotes.P3Ch02a_CurryAdj where
> import Data.Tuple (curry, uncurry, swap)

Adjunction definition from the book 
(with functional dependencies and `Representable` constraint removed)

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

This note emphasizes the intuition behind adjunction  
  `(-, a) ⊣ a -> -`    
It is is all about currying.   
These diagrams use the notation from the book
```
                   L
         (z, a) <------   z
            |             |
C((z,a),b)  |             | C(z,a->b)
           \ /           \ /
            b  ------->  a -> b
                  R
               
                L
                --- d    
              /     |
            \/      |
       (d,a)        | unit :: x -> a -> (x, a)
             \      |
              \    \ /
                --> a -> (d,a)
                R
 
            (a->c,a) <--
                  |      \
    counit ::     |       \
    (a->c,a) -> c |       a -> c
                  |      /\
                 \ /    /
                  c  --    
```                
In the instance implementation I need to have `(z, a)` flipped to `(a,z)` (because
Haskell wants `((,) a)`)               

> instance Adjunction ((,) a) ((->) a) where
>     unit :: d -> a -> (a, d)
>     unit = flip (,)    -- x a = (a,x) 
>     counit :: (a, a -> c) -> c
>     counit (x, ca) = ca x
>     leftAdjunct :: ((a, z) -> b) -> z -> a -> b
>     leftAdjunct azb = curry $ azb . swap      -- or zab a z  = zab (z,a)
>     rightAdjunct :: (z -> a -> b) -> (a, z) -> b
>     rightAdjunct zab = uncurry $ flip zab     -- or zab ~(z,a) = zab a z
 
Again, notice the need to use ugly `flip` and `swap` caused by using (a,-) and not (-,a) as the book does!
Without it we would just say:
```
leftAdjunct = curry
rightAdjunct = uncurry
```

This construction introduces two important types:
```
type State s a = s -> (a, s)
type Store s a = (s -> a, s)
```
It is empowering to know that `State` and `Store` have such a foundational importance. 

Q: what are programming implication of this adjunction for non-Hask categories? 
Such category would need to be cartesian closed and that probably means close to Hask.
Arrow - like categories may need some thought. 

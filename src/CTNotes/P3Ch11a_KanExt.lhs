|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch11a_KanExt

__Very much work-in-progress__  

Book Ref: https://bartoszmilewski.com/2017/04/17/kan-extensions/

Refs:  
http://comonad.com/reader/2011/free-monads-for-less/
http://comonad.com/reader/2011/free-monads-for-less-2/
http://comonad.com/reader/2011/free-monads-for-less-3/
http://comonad.com/reader/2008/kan-extensions/
http://comonad.com/reader/2008/kan-extensions-ii/
http://comonad.com/reader/2008/kan-extension-iii/


> {-# LANGUAGE Rank2Types
>       , ExistentialQuantification
>       , KindSignatures, PolyKinds
>       , TypeOperators
>       , MultiParamTypeClasses
>       , FunctionalDependencies
>       , FlexibleInstances
> #-}
> module CTNotes.P3Ch11a_KanExt where
> import Control.Monad
> import CTNotes.P3Ch09b_AlgebraAndFree


Ran
---
Haskell formula for Ran encodes Ran adjunction specialized to hom functor with Yoneda lemma applied:

> newtype Ran k d a = Ran (forall i. (a -> k i) -> d i)   

Pseudo-Haskell derivation. Right Kan as adjunction:
```
        
                 [I, C]          [A, C]
                          - ∘ K
                  F ∘ K <--------  F
                    |              |
  [I, C](F' ∘ K, D) |              |  [A, C](F', Ran_K D)
                   \ /            \ /
                    D  ---------> Ran_K D
                         Ran_K -

[I, C](F' ∘ K, D) ≅ [A, C](F', Ran_K D)

```
I need to show that the above formula provides isomorphism between natural transformations
```
forall ix. f (k ix) -> d ix     ≅ forall ax. f ax -> Ran k d ax
```
```
-- take f = (a ->) on both sides
forall ix. (a -> k ix) -> d ix  ≅ forall ax. (a -> ax) -> Ran k d ax
-- apply Yoneda lemma on RHS
forall ix. (a -> k ix) -> d ix  ≅ Ran k d a
```

__TODO__ For non-Hask categories (`I` non-Hask, `A` non-Hask, `C` = Hask) it could make sense to consider 
(assuming Control.Category homsetA)

> newtype CRan (homsetA:: ka -> ka -> *) (k:: ki -> ka) (d::ki -> *) (a:: ka) = CRan (forall i. (a `homsetA` (k i)) -> d i)

however there are 2 problems, first Yoneda lemma may not apply, second no free theorems for naturality condition
so the above derivation would no longer work.


Lan
---

Lan psedo Haskell derivation as an exercise.

> data Lan k d a = forall i. Lan (k i -> a) (d i)

Following more general derivation in the book, to verify this formula, 
I need to show that this is indeed the left adjoint to functor composition   

```        
                 [A, C]          [I, C]
                         Lan_K -
                Lan_K D <--------  D
                    |              |
  [I, C](F ∘ K, D)  |              |  [A, C](F, Ran_K D)
                   \ /            \ /
                    F  ---------> F ∘ K
                         - ∘ K

 [A, Set](Lan_K D, F) ≅ [I, Set](D, F'∘ K)

```

or, in psedd-Haskell:

```
forall ax. Lan k d ax -> f ax  ≅  forall ix. d ix -> f (k ix)
```
  
```  
forall ax. Lan k d ax -> f ax 
-- from definition 
≅ forall ax. forall i. Lan (k i -> ax) (d i) -> f ax 
-- currying LHS
≅ forall ax. forall i. (k i -> ax) -> (d i -> f ax)   
-- swapping universal quantification 
≅ forall i. forall ax. (k i -> ax) -> (d i -> f ax)     
-- Yoneda applied to inner forall (replaces ax with k i)
≅ forall i. d i -> f (k i)
```


Codensity, ContT, Yoneda
------------------------

Are all related of Kan extensions!  
(Ref: http://comonad.com/reader/2011/free-monads-for-less/ )

> newtype Codensity d a = Codensity {runCodensity :: forall i. (a -> d i) -> d i}  

compare to 

> newtype ContT k r m a = ContT {runContT :: (a -> m r) -> m r}

Codensity is equivalent to `Ran d d`.  Similar to `ContT` and similarly to `ContT`
`Codensity d` is always a Monad (for any type constructor `d`).
  
> instance Functor (Codensity k) where
>   fmap f (Codensity m) = Codensity (\k -> m (k . f))
> instance Monad (Codensity f) where
>  return x = Codensity (\k -> k x)
>  m >>= k = Codensity (\c -> runCodensity m (\a -> runCodensity (k a) c))
> instance Applicative (Codensity f) where
>   pure  = return
>   (<*>) = ap

```
instance MonadTrans Codensity where
   lift m = Codensity (m >>=)
``` 
ContT and Codensity both yield a result in which all of the uses of the underlying monad's (>>=) are right associated.
That makes Codensity useful in imporovig asymptotic complexity of Free monads. 

TODO `Codensity ((->) s) a` is isomorphic to `State s a`.

> class Monad m => MonadState s m | m -> s where
>   get :: m s
>   get = state (\s -> (s, s))
>   put :: s -> m ()
>   put s = state (\_ -> ((), s))
>   state :: (s -> (a, s)) -> m a
>   state f = do
>          s <- get
>          let ~(a, s') = f s
>          put s'
>          return a
>
> instance MonadState s (Codensity ((->) s)) where
>    get = Codensity (\k s -> k s s)
>    put s = Codensity (\k _ -> k () s)


Calculating Adjunctions
-----------------------
  
Ran_K I_C ⊣ K ⊣ Lan_K I_C   
or 
```
Ran K Identity ⊣ K ⊣ Lan K Identity
Ran (forall i. (a -> k i) -> i)  ⊣ K ⊣ forall i. Lan (k i -> a) i   
```

For Curry adjunction `(-, a) ⊣ a -> -`  book computes 
`Lan ((,) a) Identity b` and shows that it is isomorphic to `a -> b`.

Using the Ran against `(->) a` is even simpler

```
Ran ((->) a) Identity b
-- definition
= Ran (forall i. (b -> (a -> i)) -> i)
-- curry
≅ Ran (forall i. ((b, a) -> i) -> i)
≅ (b, a)
```

Yoneda is Functor for Free
--------------------------
Beautiful example of programming with categorical thinking.  Non-functor data constructor D
are functors from discrete category, using book notation, call it, `|Hask|`
```
 A=Hask  
  / \     \
K  |       \  Ran_K D
   |        \/ 
I=|Hask| --> C=Hask
         D
```
K is the natural embedding of `|Hask|` into `Hask`.  
Remember we had
```
Ran_K D a ≅ ∫i Set(A(a, K i), D i)
```
which still translates to since A=Hask
```
newtype Ran k d a = Ran (forall i. (a -> k i) -> d i) 
```
and since K is type level Identity
```
newtype FreeF d a = RanF (forall i. (a -> i) -> d i) 
```
which is really (see [N_P2Ch05a_YonedaAndMap](N_P2Ch05a_YonedaAndMap))
```
newtype Yoneda d a = Yoneda (forall i. (a -> i) -> d i) 
```
That explains why Yoneda creates monads for Free.

Similarly (see [N_P2Ch05a_YonedaAndMap](N_P2Ch05a_YonedaAndMap))
```
data CoYoneda f a = forall x. CoYoneda (x -> a) (f x)
```
is isomorphic to the type derived in the book using Lan_K D approach
```
data FreeF f a = forall i. FMap (i -> a) (f i)
```

|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch11a_KanExt

Notes about CTFP Part 3 Chapter 11. Kan Extensions
==================================================

This note covers:
* Haskell (simplified) derivations of Ran and Lan.  
* Similarities of Codensity, ContT, Yoneda.  
* Example of calculating adjunctions.  
* That beautiful argument about how Yoneda creates functors for free using Haskell code.

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
> import CTNotes.P3Ch09a_Talg


Ran, Haskell derivation
-----------------------
Haskell formula for Ran (right Kan extension): 

> newtype Ran k d a = Ran (forall i. (a -> k i) -> d i)   

Here is this how this formula is derived from the right Kan adjunction
(Ran is right-adjunct of functor composition)
```
        
                 [I, C]          [A, C]
                          - ∘ K
                 F' ∘ K <--------  F'
                    |              |
  [I, C](F' ∘ K, D) |              |  [A, C](F', Ran_K D)
                   \ /            \ /
                    D  ---------> Ran_K D
                         Ran_K -

[I, C](F' ∘ K, D) ≅ [A, C](F', Ran_K D)

```
Pseudo-Haskell representation of the above diagram is
```
forall ix. f (k ix) -> d ix     ≅ forall ax. f ax -> Ran k d ax
```
take f = (a ->)
```
forall ix. (a -> k ix) -> d ix  ≅ forall ax. (a -> ax) -> Ran k d ax
```
and apply Yoneda lemma on RHS
```
forall ix. (a -> k ix) -> d ix  ≅ Ran k d a
```

So, Haskell Ran is basically Ran adjunction specialized to the hom functor with Yoneda lemma applied.


Q: For non-Hask categories (as in [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats)) it makes sense to consider 
(assuming homsetA implementing Control.Category, `I` is non-Hask, `A` is non-Hask, and `C` = Hask))

> newtype CRan (homsetA:: ka -> ka -> *) (k:: ki -> ka) (d::ki -> *) (a:: ka) = 
>    CRan (forall i. (a `homsetA` (k i)) -> d i)

A: there are 2 problems, first: Yoneda lemma is no longer
that simple ([N_P2Ch05b_YonedaNonHask](N_P2Ch05b_YonedaNonHask)), 
second: we no longer have free theorems for naturality condition 
[N_P1Ch10b_NTsNonHask](N_P1Ch10b_NTsNonHask).
So the above derivation no longer holds.


Lan, Haskell derivation
-----------------------

Haskell formula for Lan.

> data Lan k d a = forall i. Lan (k i -> a) (d i)

Following a more general derivation in the book, to verify this formula, 
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

or, in psedo-Haskell:

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
Are all related to Kan extensions!  

Kan extensions have almost universal importance and applicability. 
Quoting [Ch 15](https://bartoszmilewski.com/2017/09/06/monads-monoids-and-categories/): 
"There is a saying that all concepts are Kan extensions and, indeed, you can use Kan extensions to derive 
limits, colimits, adjunctions, monads, the Yoneda lemma, and much more."

This part of the note follows the above [commonad post](http://comonad.com/reader/2011/free-monads-for-less/)
to explore similarities between Codensity, and ContT, and Yoneda type constructors.

> newtype Codensity d a = Codensity {runCodensity :: forall i. (a -> d i) -> d i}  

compare to 

> newtype ContT k r m a = ContT {runContT :: (a -> m r) -> m r}

and to (see [N_P2Ch05a_YonedaAndMap](N_P2Ch05a_YonedaAndMap))
```
newtype Yoneda d a = Yoneda (forall i. (a -> i) -> d i) 
```

Codensity is equivalent to `Ran d d`, `Yoneda d` is `Ran id d`.  
Similarly to `ContT`
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
That makes Codensity useful in improving asymptotic complexity of Free monads. 

A very interesting fact is that `Codensity ((->) s) a` is isomorphic to `State s a`

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
Adjunctions can be calculated with help of the following formula
```
-- Ran_K I_C ⊣ K ⊣ Lan_K I_C

Ran K Identity ⊣ K ⊣ Lan K Identity
Ran (forall i. (a -> k i) -> i)  ⊣ K ⊣ forall i. Lan (k i -> a) i   
```

For Curry adjunction `(-, a) ⊣ a -> -` the book computes 
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


Yoneda and Functors for Free
----------------------------
A beautiful example of programming with categorical thinking from the book.  
Non-functor data constructor D
are functors from the corresponding discrete category, using book notation, call it, `|Hask|`
```
 A=Hask  
  / \     \
K  |       \  Ran_K D
   |        \/ 
I=|Hask| --> C=Hask
         D
```
K is the natural embedding of `|Hask|` into `Hask`.  
Remember, we have
```
Ran_K D a ≅ ∫_i Set(A(a, K i), D i)
```
which translates (since A=Hask) to the same Ran definition:
```
newtype Ran k d a = Ran (forall i. (a -> k i) -> d i) 
```
and since K is just type level Identity, this is equivalent to (using `FreeF` name from the book)
```
newtype FreeF d a = RanF (forall i. (a -> i) -> d i) 
```
which is really (see the definition above)
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

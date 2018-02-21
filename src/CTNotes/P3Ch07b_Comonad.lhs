|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch07b_Comonad

Notes related to CTFP Part 3 Chapter 7. Comonads
================================================

Loose notes about commonads focused on the focus intuition and code examples.

Book reference:
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)
[P3 Ch7 Comonads](https://bartoszmilewski.com/2017/01/02/comonads/).

> {-# LANGUAGE InstanceSigs
>  , ScopedTypeVariables
>  #-}
>
> module CTNotes.P3Ch07b_Comonad where
> import Control.Comonad
> import Utils.Stream
> import CTNotes.P3Ch07a_GameOfLife (Store(..))

Laws
```
extract . duplicate      = id
fmap extract . duplicate = id
duplicate . duplicate    = fmap duplicate . duplicate
```

Explicit/Implicit focus
-----------------------
Comonads are pointed spaces (spaces with focus point) containing possible application states. 
Focus point can be explicit (like in Store) or implicit (like in Stream).
With explicit focus point there seems to be less work implementing Comonad instance but more work 
implementing co-arrows.

__Example__  
As pointed out in the book, Stream can be easily made bidirectional.

> data BidiStream a = BidiStream (Stream a) a (Stream a) 
> data Nav = B | F
> 
> move :: Nav -> BidiStream a -> BidiStream a
> move F (BidiStream (Cons x xneg) xa xpos) =  BidiStream xneg x (Cons xa xpos)
> move B (BidiStream xneg xa (Cons x xpos)) =  BidiStream (Cons xa xneg) x xpos
>
> streamIterate' :: (a -> a) -> a -> Stream a
> streamIterate' f x = Cons (f x) (streamIterate' f (f x))
>
> instance Functor BidiStream where
>    fmap f (BidiStream as1 a as2) = BidiStream (fmap f as1) (f a) (fmap f as2)
>
> instance Comonad BidiStream where
>    extract :: BidiStream a -> a
>    extract (BidiStream _ a _) = a
>    duplicate :: BidiStream a -> BidiStream (BidiStream a)
>    duplicate line = BidiStream (streamIterate' (move F) line ) line (streamIterate' (move B) line)

This has implicit (center) focus point. Arrows are simple and have more 'hardcoded' feel.

> avg3 :: BidiStream Double -> Double   
> avg3 (BidiStream (Cons b1 _) c (Cons a1 _)) = b1 + c + a1 / 3
>
> movingAvg :: BidiStream Double -> BidiStream Double
> movingAvg  = extend avg3 

Compare this to

> data MyNatural = One | Succ MyNatural
> data MyInt = Neg MyNatural | Zero | Pos MyNatural
>
> type IntStore a = Store MyInt a
>
> avg3' :: IntStore Double -> Double   
> avg3' (Store f s) = 
>        (f (pred s)) + (f s) + (f (succ s)) / 3
>        where pred :: MyInt -> MyInt
>              pred = undefined -- that great lambda calc exercise again
>              succ :: MyInt -> MyInt
>              succ = undefined
>
> movingAvg' :: IntStore Double -> IntStore Double
> movingAvg'  = extend avg3' 

`avg3'` needs to operate on specified focus point making it just slightly harder to implement. 
But the Commonad instance is much less work for the Store!

Note, BidiStream type is isomorphic to 

> newtype BiDiLine a = BiDiLine (MyInt -> a)

and Stream is isomorphic to

> newtype HalfLine a = HalfLine (MyNatural -> a)
>
> iso1 :: HalfLine a -> Stream a
> iso1 (HalfLine f) = Cons (f One) (iso1 (HalfLine (f . Succ)))
>
> iso2 :: Stream a -> HalfLine a
> iso2 stream = 
>     let f :: Stream a -> MyNatural -> a
>         f (Cons a _) One = a
>         f (Cons _ ax) (Succ n) = f ax n
>     in HalfLine $ f stream

and both `BiDiLine` `HalfLine` look like Store without a focus point.
Both could can easily implement Comonad instance.

Interesting Comonads 
--------------------
* Some Comonads that are also Monads: NonEmpty List, Tree, `(,) e`
* CoFree is out of scope for this note

__Traced__  
HalfLine focus point would be `One`, for `BiDiLine` would be `Zero`. `Traced` provides this
interesting twist:

> data Traced m a = Traced {runTraced:: m -> a}
> instance Functor (Traced m) where
>    fmap f (Traced f0) = Traced (f . f0)
> instance Monoid m => Comonad (Traced m) where
>    extract (Traced f) = f mempty
>    duplicate (Traced f) = Traced (\m1 -> Traced (\m2 -> f (m2 `mappend` m1))) 

Traced uses monoid m to point to (focus on) information what can be retrieved using it.
Traced extends to a comonad transformer (defined in the `comonad` package). 

__Zipper__  
My implementation `BidiStream` is sometimes referred to as Zipper comonad.
More judicious Zipper based on finite lists:

> data Zipper a = Zipper [a] a [a]
> instance Functor Zipper where
>    fmap f (Zipper ax1 a ax2) = Zipper (map f ax1) (f a) (map f ax1)
> instance Comonad Zipper where
>    extract (Zipper ax1 a ax2) = a
>    duplicate z = Zipper (iterateLeft z) z (iterateRight z)
>         where
>             iterateLeft :: Zipper a -> [Zipper a] 
>             iterateLeft (Zipper [] a rs) = []
>             iterateLeft (Zipper (l:ls) a rs) = let nz = Zipper ls l (a:rs) in nz : iterateLeft nz
>             iterateRight :: Zipper a -> [Zipper a] 
>             iterateRight (Zipper ls a []) = []
>             iterateRight (Zipper ls a (r:rs)) = let nz = Zipper (a:ls) r rs in nz : iterateRight nz

`duplicate` returns a zipper where each element is itself a zipper focused on the corresponding element in the original zipper.
`extend` is like a map only with access to all elements in the zipper, not just one. 
Supposedly, every zipper is a comonad.

__Tree__  

> data Tree a = Node a [Tree a]
> instance Functor Tree where
>    fmap f (Node x ts) = Node (f x) (map (fmap f) ts)
> instance Comonad Tree where
>    extract (Node a _) = a
>    duplicate n@(Node _ as) = Node n (map duplicate as)

`extract` returns root label, `duplicate` replaces all labels with a corresponding tree.


__Refs:__
http://blog.functorial.com/posts/2016-08-07-Comonads-As-Spaces.html
http://comonad.com/reader/2011/monads-from-comonads/  
* CoFree is out of scope for this note. I will add notes about Cofree in 
[N_P3Ch08b_FalgFreeMonad](N_P3Ch08b_FalgFreeMonad).


Notes
-----
Monads preserve product, comonads coproduct.
```
(Comonad f, Comonad g) => Comonad (Sum f g)
```

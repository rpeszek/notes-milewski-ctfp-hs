TODO work in progress

CTFP Part 1 Chapter 10. Natural Transformations
===============================================
If good programming is about composability than we got to study Natrual Tranformations!
They can be composed in more than one way.
These notes assume familiarty with CTFP Ch 10.

> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE TypeOperators #-}
>
> module CTNotes.P1Ch10_NaturalTransformations where
>
> import qualified Control.Category as Cat
> import CTNotes.P1Ch07_Functors_Composition ((:.))
> import qualified CTNotes.P1Ch07_Functors_Composition as FComp

Typically Natural Transformations (NTs) are defined using ~> type operator.
This is the case for Scalaz and Purescript. To keep with my convention of prefixing
type operators with (:) I will define as (:~>).  Otherwise this definiton matches the book.

> infixr 0 :~>
> type f :~> g = forall x. f x -> g x

This means functions from type f x to type g x that are polymorphic in x.  For example
```
safeHead :: [] :~> Maybe  -- typical signature would be [a] -> Maybe a
```
Vertical composition of NT-ies reduces to (.). Compostion of 2 functions that happen to be polymorphic must also be polymorphic.

> verticalComp :: g :~> h -> f :~> g -> f :~> h
> verticalComp gh fg = gh . fg

Recap. Naturality condition
---------------------------
We are intersted in functions ```f a -> g b```.
Natural tranformation allows as to move between functors, fuction a -> b moves us between types.
Combining these to we can change both functor and type.  Having both in our disposal allows us to accomplish what we want
in two different ways:

> naturality1 :: Functor g => f :~> g -> (a -> b) -> f a -> g b
> naturality1 alpha f = fmap f . alpha
>
> naturality2 :: Functor f => f :~> g -> (a -> b) -> f a -> g b
> naturality2 alpha f = alpha . fmap f

CT definition of Natural Transformation says that both approaches need to commute (yield the same result).
What is amazing is that in programming you get this for FREE!  Compiler can safely replace code like naturality1 with
code for naturality2 if it feels like it will make thing better or faster.
I think this can happen if both f and g are functors (but maybe I am wrong and f suffices).
The actual CT formula should be
```
   fmap_G f . alpha_a == alpha_b . fmap_F f
```
but because alpha is polymorphic we can drop types _a and _b from the formula and compiler can reconstruct/infer which functor type
to use for fmap.

Functor Category
----------------

> newtype NTVert f g = NTVert { ntVert :: f :~> g }

> instance Cat.Category (NTVert) where
>    id = NTVert id
>    NTVert f . NTVert g = NTVert (f `verticalComp` g)


Horizontal Composition
----------------------
Horizontal composition of NT-ies is NT between composed functors, repeating the book:
α :: F -> F'
β :: G -> G'
β ∘ α :: G ∘ F -> G'∘ F'

In general we would have something like
    G'α_a ∘ β_F a  == β_F'a ∘ G α_a

but parametricity/polymorphism arguments allow us to write simple code.

> horizontalComp1 :: Functor g =>
>                     g :~> g' -> f :~> f' -> g :. f :~> g' :. f'
> horizontalComp1 beta alpha =
>    (\(FComp.FCompose x) -> FComp.FCompose $ beta . fmap alpha $ x)

> horizontalComp2 :: Functor g' =>
>                    g :~> g' -> f :~> f' -> g :. f :~> g' :. f'
> horizontalComp2 beta alpha =
>    (\(FComp.FCompose x) -> FComp.FCompose $ fmap alpha . beta $ x)

Note all of these should be Functors but for the implementation we just need one.
Again, commuting diagrams say that ```horizontalComp1 '==' horizontalComp2```

(.) represents Hask morphism
Note a much simpler implementation
fmap (beta . fmap alpha)
with this error
 Expected type: (:.:) b1 a1 x -> (:.:) b2 a2 x
    Actual type: FComp.FCompose b2 a2 (b1 (a1 x0))
                 -> FComp.FCompose b2 a2 (b2 (a2 x0))
this is because fmap acts on x in FCompose a b x leaving a and b unchanged

TODO distribution law
TODO can we express Category that uses horizontalComp in Haskell?
TODO real life examples of NTs
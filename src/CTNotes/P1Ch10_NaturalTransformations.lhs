TODO work in progress

CTFP Part 1 Chapter 10. Natural Transformations
===============================================

If good programming is about composability than we got to study Natural Transformations (NTs for short).
NTs can be composed in more than one way.
These notes assume familiarity with 
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 10](https://bartoszmilewski.com/2015/04/07/natural-transformations/).

> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE TypeOperators #-}
>
> module CTNotes.P1Ch10_NaturalTransformations where
>
> import qualified Control.Category as Cat
> import CTNotes.P1Ch07_Functors_Composition ((:.))
> import qualified CTNotes.P1Ch07_Functors_Composition as FComp

Typically Natural Transformations (NTs) are defined using `~>` type operator.
This is the case for Scalaz and Purescript. To keep with my convention of prefixing
type operators with `:` I will define it as `:~>`.  Otherwise, this definition matches the book.

> infixr 0 :~>
> type f :~> g = forall x. f x -> g x

This means functions from type `f x` to type `g x` that are polymorphic in type parameter x.  For example, we could write

> safeHead :: [] :~> Maybe  
> safeHead [] = Nothing
> safeHead (x:xs) = Just x

instead of 
```
safeHead :: [a] :~> Maybe a
```

Recap. Vertical Composition
---------------------------
Vertical composition of NT-ies reduces to `(.)`. Composition of 2 functions that happen to be polymorphic must also be polymorphic.

> verticalComp :: g :~> h -> f :~> g -> f :~> h
> verticalComp gh fg = gh . fg


Recap. Naturality condition
---------------------------
We are interested in functions `f a -> g b`.
Natural transformation allows as to move between functors `f` and `g`, function `a -> b` moves us between types.
Combining these, allows to change both functor and type and move `f a -> g b`.  
However, we can accomplish that in two different ways:

> naturality1 :: Functor g => f :~> g -> (a -> b) -> f a -> g b
> naturality1 alpha f = fmap f . alpha
>
> naturality2 :: Functor f => f :~> g -> (a -> b) -> f a -> g b
> naturality2 alpha f = alpha . fmap f

(Read this as: if I have an NT `f :~> g` and a function `(a -> b)`, I can change both `f a -> g b`.)   
Category Theoretical definition of Natural Transformation says that both approaches need to commute (yield the same result).
What is amazing is that in programming you get this for FREE!  Static code analysis can safely replace one code with
the other if it feels like it will make thing better or faster.   
TODO: I think this can happen if both f and g are functors (but maybe I am wrong and f suffices).  

The actual formula in Category Theory repeated from the book is:
```
   fmap_G f . alpha_a == alpha_b . fmap_F f
```
but because alpha is polymorphic we can drop underscored types `a` and `b`. Compiler can reconstruct/infer which functor type
to use for fmap and this can be dropped as well.


Functor Category
----------------
Functors form a category (Functors are objects and NTs are morphisms). 
We can express this using `Category` typeclass defined in Control.Category module included in the base package.

> newtype NTVert f g = NTVert { ntVert :: f :~> g }
>
> instance Cat.Category (NTVert) where
>    id = NTVert id
>    NTVert f . NTVert g = NTVert (f `verticalComp` g)

(`id` in `NTVert id` is the polymorphic identity `id :: a -> a` function.)  
Proving the category laws is trivial since the vertical composition reduces to function composition.


Horizontal Composition
----------------------
Horizontal composition of NT-ies is an NT between composed functors, repeating the book:  
 α :: F -> F'  
 β :: G -> G'  
 β ∘ α :: G ∘ F -> G'∘ F'  

In general we would have something like  
    G'α_a ∘ β_F a  == β_F'a ∘ G α_a

β ∘ α is sometimes called Godement product and the above isomorphism Godement interchange law.

Parametricity/polymorphism arguments make horizontal composition simpler in Haskell:

> horizontalComp1 :: Functor g =>
>                     g :~> g' -> f :~> f' -> g :. f :~> g' :. f'
> horizontalComp1 beta alpha =
>    (\(FComp.FCompose x) -> FComp.FCompose $ beta . fmap alpha $ x)
>
> horizontalComp2 :: Functor g' =>
>                    g :~> g' -> f :~> f' -> g :. f :~> g' :. f'
> horizontalComp2 beta alpha =
>    (\(FComp.FCompose x) -> FComp.FCompose $ fmap alpha . beta $ x)

Again, since we have `horizontalComp1 '==' horizontalComp2` static code analysis can swap one code for the other.  
This is really nice!

Note 1: In the above formulas (from the CT point of view) (.) represents Hask morphism so it should be viewed as 
function composition, not vertical composition of NTs.   
Note 2: all of these should be Functors but for the implementation we just need one.  
TODO: do we need all of them to be functors for the interchange law to hold in Haskell?  
Note 3: a much simpler implementation `fmap (beta . fmap alpha)` does not compile.  
GHC infers the same types on both sides:
```  
 Expected type: (:.:) b1 a1 x -> (:.:) b2 a2 x  
    Actual type: FComp.FCompose b2 a2 (b1 (a1 x0))
                 -> FComp.FCompose b2 a2 (b2 (a2 x0))
```



TODO  interchange law:     
      (β' ⋅ α') ∘ (β ⋅ α) = (β' ∘ β) ⋅ (α' ∘ α)
      in Haskell

TODO can we express Category that uses horizontalComp in Haskell? I doubt. 

TODO real life examples of NTs

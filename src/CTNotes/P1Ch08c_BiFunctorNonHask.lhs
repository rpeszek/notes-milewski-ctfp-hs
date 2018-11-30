|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch08c_BiFunctorNonHask

Notes about CTFP Part 1 Chapter 8. Functoriality. BiFunctor generalized to non-Hask categories.
===============================================================================================

In this note, I define more general version of bifunctor that is similar in spirit to CFunctor.
This, more general bifunctor is needed for future use (monoidal categories [N_P3Ch06c_MonoidalCats](N_P3Ch06c_MonoidalCats)). 

Refs: `category-extras`, `categories` packages

> {-#LANGUAGE MultiParamTypeClasses
>  , PolyKinds
>  , FlexibleInstances
>  #-}
> module CTNotes.P1Ch08c_BiFunctorNonHask where
> import Control.Category
> import Prelude hiding ((.), id)
> import qualified Control.Arrow as Arr

`category-extras` and `categories` define `Monoidal` in terms of more general type classes: `Associative`, `Bifunctor`, 
and `HasIdentity`.
This note bundles all 3 into one and uses a less generic approach.

> class (Category r, Category t) => CBifunctor bi r t where
>      bimap :: r a c -> r b d -> t (bi a b) (bi c d)
>      bimap g h = first g . second h
>      first :: r a c -> t (bi a b) (bi c b)
>      first g = bimap g id
>      second :: r b d -> t (bi a b) (bi a d)
>      second = bimap id

Read `r a c` as `homset_r a c` and `t (bi a b) (bi c d)` as `homset_t (bi a b) (bi c d)`.  
This definition assumes bifunctor `R x R -> T` (instead a more general functor `R x S -> T` in `category-extras`).
Also instead of using Functor constraints it simply lists first and second projections.
For simplicity, I have also omitted functional dependencies.

Some obvious example instances: 


> instance {-# OVERLAPS #-} CBifunctor Either (->) ((->)) where
>       bimap f _ (Left a) = Left (f a)
>       bimap _ g (Right a) = Right (g a)
>
> instance {-# OVERLAPS #-} CBifunctor (,) (->) (->) where
>      bimap f g ~(a,b)= (f a, g b)

(the code below (arrows) is more generic hence the use of `OVERLAPS`) 

I will use this generalized version of bifunctor in the future.

`Control.Arrow`
---------------
We know (see above) that `(,)` is a bifunctor under Hask 
(category based on on `(->)` morphisms).  What are some other categories where 
`(,)` is a bifunctor?  A bunch of such categories is called arrows.

Here is the typeclass definition from the base package (quoted only):
```
class Category a => Arrow a where
    arr :: (b -> c) -> a b c
    (***) :: a b c -> a b' c' -> a (b,b') (c,c')
    f *** g = first f >>> arr swap >>> first g >>> arr swap
        where swap ~(x,y) = (y,x)
    first :: a b c -> a (b,d) (c,d)
    first = (*** id)
    second :: a b c -> a (d,b) (d,c)
    second = (id ***)
    (&&&) :: a b c -> a b c' -> a b (c,c')
    (&&&) = ...
```
Compare this against the above `CBifunctor`. Set
```
r = a
t = a
bi = (,)
```
Notice `first` is `first`, `second` is `second` and `bimap` is `***`.
Basically arrows can be viewed as a category that generalized `(->)` and still
allows `(,)` to be bifunctor.

> instance Arr.Arrow arr => CBifunctor (,) arr arr where
>   bimap = (Arr.***)

We can ask the same question about `Either` bifunctor.  Here is a bunch of categories 
that keep both `(,)` and `Either` as bifunctors:

```
class Arrow a => ArrowChoice a where
    (+++) :: a b c -> a b' c' -> a (Either b b') (Either c c')
    f +++ g = left f >>> arr mirror >>> left g >>> arr mirror
      where
        mirror :: Either x y -> Either y x
        mirror (Left x) = Right x
        mirror (Right y) = Left y
    left :: a b c -> a (Either b d) (Either c d)
    left = (+++ id)
    right :: a b c -> a (Either d b) (Either d c)
    right = (id +++)
    (|||) :: a b d -> a c d -> a (Either b c) d
    (|||) = ...
```
`first` is `left`, `second` is `right` and `bimap` is now `(+++)`.

> instance Arr.ArrowChoice arr => CBifunctor Either arr arr where
>   bimap = (Arr.+++)

Nice!

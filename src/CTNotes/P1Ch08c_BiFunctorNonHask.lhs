|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch08c_BiFunctorNonHask

For my own future use (Monoidal Categories) I define more general version of BiFunctor that is similar in spirit to CFunctor.

Refs: `category-extras`, `categories` packages

> {-#LANGUAGE MultiParamTypeClasses, PolyKinds#-}
> module CTNotes.P1Ch08c_BiFunctorNonHask where
> import Control.Category
> import Prelude hiding ((.), id)

`category-extras` and `categories` define Monoidal in terms of more general type classes: `Associative`, `Bifunctor`, 
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
For simlicity, I have also ommited functional dependencies.

Some obvious example instances 

> instance CBifunctor Either (->) ((->)) where
>        bimap f _ (Left a) = Left (f a)
>        bimap _ g (Right a) = Right (g a)
>
> instance CBifunctor (,) (->) (->) where
>        bimap f g ~(a,b)= (f a, g b)

I will use this generalized version of bifunctor in the future.
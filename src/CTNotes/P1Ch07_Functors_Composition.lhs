|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch07_Functors_Composition

Notes about CTFP Part 1 Chapter 7. Functors - Functor Composition
=================================================================

The last section of 
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 7](https://bartoszmilewski.com/2015/01/20/functors/)
talks about composition of functors 
and about how functors themselves can be viewed as morphisms in another 'higher' category.
This is my attempt to use Haskell language to describe these concepts.  

What are the properties of types like `[Tree (Either Err [a])]`, `Either Err (Parser [a])` or 
`(r -> [(s -> Maybe (t -> ))])`?   
In my opinion, functor composition is foundational to understanding of even basic types like nested lists 
`[[a]]` or something like `safeTail::`Maybe [a]`.

> {-# LANGUAGE TypeOperators 
>  , TypeFamilies 
>  , LiberalTypeSynonyms 
>  #-}
>
> module CTNotes.P1Ch07_Functors_Composition where
> import Data.Functor.Compose (Compose(..))
> import Data.Functor.Identity (Identity(..))

Functor composition
-------------------
Expressing functor composition is surprisingly doable in Haskell. It is implemented in the
imported `Data.Functor.Compose` module (`base` package).  I am quoting abbreviated definition for documentation purposes:

```
newtype Compose f g a = Compose { getCompose :: f (g a) }
instance (Functor f, Functor g) => Functor (Compose f g) where
    fmap f (Compose x) = Compose (fmap (fmap f) x)
```

Instead of direct composition like `Maybe [a]` this creates an isomorphic type `Compose Maybe [] a`.  
Haskell has no problem with writing types like `(a -> b) -> f (g a) -> f (g b)` but
using this nominal typing trick allows us to get a hook to actually program with type level composition!   
The book uses `G ∘ F` notation for function composition. To mimic this, I create a type operator
(requires `TypeOperators` pragma). I am using colon `:` to make it clear that this is a type level operator.

> type f :. g = Compose f g

This way `Maybe :. []` becomes a functor that maps type `Int` into `Maybe [Int]` and I can write code like this:

> safeTail :: [a] -> (Maybe :. []) a
> safeTail [] = Compose Nothing
> safeTail (x:xs) = Compose $ Just xs 

Well, it really maps `Int` to `Compose Maybe [Int]`, but that is that up-to isomorphisms limitation caused
by using `newtype`.


Identity
--------
Identity functor is introduced in the book in Chapter 8.  I will use definition from the `base` package `Data.Functor.Identity` module. 
Here is the definition (it is a quote, not actual code, since I am importing it):

```
newtype Identity a = Identity { runIdentity :: a }
instance Functor Identity where
   fmap f (Identity x) = Identity (f x)
```

As before, `Identity` is only up to isomorphism, which amounts to constructing with `Identity` and deconstructing with `runIdentity`.


Category Laws
-------------
We can compose functors and we also have identity functor.  To have a category in which functors are morphisms
we need to verify category laws.
The most interesting is the check that composition is associative
(again, up to isomorphism because `Compose` data constructor will need to move around).    
This is done by explicitly defining the isomorphisms:

> isoFCA1 :: Functor f => ((f :. g) :. h) a -> (f :. (g :. h)) a
> isoFCA1 (Compose (Compose fgh_x)) = Compose (fmap Compose fgh_x)
>
> isoFCA2 :: Functor f => (f :. (g :. h)) a -> ((f :. g) :. h) a
> isoFCA2 (Compose f_comp_ghx) =  Compose (Compose $ fmap getCompose f_comp_ghx)

Simple equational reasoning shows that `isoFCA1` and `isoFCA2` are indeed inverses of each other.
For example, this shows that `isoFCA2 . isoFCA1` reduces to identity:
```
 isoFCA2 . isoFCA1 $ Compose (Compose fgh_x)              ==  -- definition of isoFCA1
 isoFCA2 $ Compose (fmap Compose fgh_x)                   ==  -- definition of isoFCA2
 Compose (Compose $ fmap getCompose (fmap Compose fgh_x)) ==  -- functors preserve morphism composition
 Compose (Compose $ fmap (getCompose . Compose) fgh_x)    ==  -- getCompose deconstructs Compose
 Compose (Compose $ fmap id fgh_x)                        ==  -- functors preserve identity morphisms
 Compose (Compose fgh_x)
```
(`isoFCA2 . isoFCA1` is identity on `((f :. g) :. h) a`.)   
Left and right identity laws are equally easy to verify.


Equi-composition
----------------
We are forced to deal with isomorphism because of `newtype`. A more structural type composition would produce
strict equality (`LiberalTypeSynonyms` pragma is required to do this): 

> type Comp f g a = f (g a)
> associativity :: Comp f (Comp g h) a -> Comp (Comp f g) h a
> associativity = id

This seems somewhat analogous to the equi-recursion vs iso-recursion ideas in language design,
except wrapping and unwrapping (using `Compose` and `getCompose`) is not handled automatically at the language level.
Because of this similarity I am calling it (probably not a very good name) equi-composition.  
I am not pursuing this direction here.  `newtype` seems just a simpler way to go in Haskell (for example, 
I have little and on a negative side experience with `-XTypeSynonymInstances` pragma).  
On intuitive level, it seems that this direction would be easier on the programmer and 
much harder on the language.


Typing it
----------------------
Haskell base package `Control.Category` module contains `Category` typeclass.
This typeclass allows to express what it means to be a category:

```
class Category cat where
     id :: cat a a
     (.) :: cat b c -> cat a b -> cat a c

instance Category (->) where ...
instance Category (:~:) where ...

```
Proof obligation of checking the laws is left to the programmer.

This is perfect for defining categories when objects are just types.
To do something analogous and define a category in which morphisms are functors, we need to lift ourselves one level up
and deal with kinds.  
(Kinds are a way for compiler to check type level expressions.  Kinds are 'types of types'.)  
If 'normal' categories are about types and functions, out category needs to be about kinds and type level functions.
I use `KCategory` name to indicate that (using K for kind).
Haskell `TypeFamilies` pragma allows me to define a constraint analogous to `Control.Category.Category`.

> class KCategory cat where
>    type KId cat :: * -> *
>    type KComp cat :: (* -> *) -> (* -> *) -> * -> *

Notice that this is less typed than what we get with `Control.Category.Category` typeclass.
For example `id :: cat a a` guarantees that `a` is the same on both sides, we no longer have such a guarantee.


Monster Category we are looking for
-----------------------------------
Functor domain and co-domain consist of types of kind `*`.  We can think of set of all these types as one object.
Category where morphisms are Haskell functors is, thus, a monster monoid.  I will just call it Monster.

> data Monster = Monster
> instance KCategory Monster where
>    type KId Monster = Identity
>    type KComp Monster = Compose

Moving from types to kinds makes thinks less interesting. The only interesting thing here is that I can actually express
this in the language.


Stronger Type Checking of the Monster
-------------------------------------
I can do better and try to match the level of type checking done by `Control.Category.Category`.
Remember, we can only hope for type isomorphism.
For example, `Identity Bool` is not the same as `Bool`, but is isomorphic to `Bool`.

> data Iso a b = IsoProof {
>     isoRight :: a -> b,
>     isoLeft :: b -> a
> }

As is to be expected, the proof obligation that `isoRight` and `isoLeft` are inverses of one another will be left to the programmer 
but in our case that proof will be trivial.

> class KCategory2 cat where
>   data KId2 cat :: * -> *
>   data KComp2 cat :: (* -> *) -> (* -> *) -> * -> *
>   idIsoEvidence :: Iso a (KId2 cat a)
>   compIsoEvidence :: (Functor f, Functor g) => Iso (f (g a)) (KComp2 cat f g a)

And here is the improved version:

> instance KCategory2 Monster where
>    data KId2 Monster x = MkId {getMkId:: Identity x}
>    data KComp2 Monster f1 f2 x = MkComp {getMkComp:: Compose f1 f2 x}
>    idIsoEvidence =  IsoProof (MkId . Identity) (runIdentity . getMkId)
>    compIsoEvidence = IsoProof (MkComp . Compose) (getCompose . getMkComp)

The proofs of isomorphisms are trivial and boil down to construction and deconstruction for
`MkComp`, `Compose`, `Identity`, and `MkId`.

Notice that `KCategory` uses `type` keyword (is a type synonym family) and `KCategory2` uses a somewhat more tedious `data`
(is a data family). This is because, for complex reasons, type synonym classes are more permissive and may be not injective.
GHC compiler does not allow me to define the Iso constraints `idIsoEvidence` or `compIsoEvidence` using
the type synonym approach.  (TODO I lack more detailed understanding.)


Polymorphic Composition
-----------------------
Edward Kmett's `comonad` package (`Data.Functor.Composition` module) includes typeclass definition to allow for a more 
uniform treatment of various implementations of functor composition.  This definition is repeated (quoted) here: 

```
class Composition o where
   decompose :: o f g x -> f (g x)
   compose :: f (g x) -> o f g x
```

together with implementation of its instance for `Data.Functor.Compose`:

```
instance Composition Compose where
   decompose = getCompose
   compose = Compose
```


Code examples
-------------
Functor composition provides a theoretical framework for working with and understanding nested types. 
In day-to-day work I am dealing with 'hardcoded' types like `[[Int]]` or `Maybe [Int]` and do not think 
much about their theoretical properties.
Is there any direct benefit of polymorphic, programmable composition of type constructors?  
Here is one fun example:

> nestedList :: ([] :. []) Int
> nestedList = Compose [[1,2,3], [4,5,6]]
> adjustedList = fmap (+1) nestedList

Look ma, only one `fmap`! (no `fmap` == no teeth)  
`adjustedList` contains `Compose [[2,3,4],[5,6,7]]`.  How cool!  
Another example:

> maybeList :: (Maybe :. []) Int
> maybeList =  Compose $ Just [1,2,3]
> adjustedList2 = fmap (+1) maybeList

or something crazy like this:

> nested :: (((->) Int) :. ([] :. ((->) Int))) Int
> nested = Compose (\i -> Compose $ map (+) [0..i])
> adjusted3 :: (((->) Int) :. ([] :. ((->) Int))) Int
> adjusted3 = fmap (+1) nested

I can write polymorphic code (here `fmap (+1)`) against nested types.  Even cooler!

But it gets even better and more interesting.  `Compose` (from `Data.Functor.Compose`) has instances of `Foldable`, 
`Traversable`, `Applicative` allowing for interesting polymorphic access when programming with nested types.


Monad Limitation 
----------------
Notice instance of `Applicative` and no instance of `Monad` for `Data.Functor.Compose. 
The composition of (applicative) functors is always (applicative) functor.
Functor composition is essential in the categorical definition of Monad but 
the composition of monads is not always a monad (that is why we need that MTL library).  
I will investigate this more in [N_P3Ch06a_CTMonads](N_P3Ch06a_CTMonads) 


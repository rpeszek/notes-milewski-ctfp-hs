|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch09a_Talg

Notes about CTFP Part 3 Chapter 9. Algebras for monads
======================================================

A side note about the structure of the category of monad algebras for the monad obtained from 
any free-forgetful adjunction.  This generalizes the List monad algebra example in the book. 

> module CTNotes.P3Ch09a_Talg where

Book Ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch.9. Algebras for Monads](https://bartoszmilewski.com/2017/03/14/algebras-for-monads/)

Ref: [Doel, schoolofhaskell](https://www.schoolofhaskell.com/user/dolio/many-roads-to-free-monads).  


Some interesting facts about monad algebra
------------------------------------------
__Recap__ Monad algebras (T-algebras) differ from F-algebras in that they assume additional 
coherence conditions between the eval function 
`T a -> a` and the two natural transformations defining monad `η :: a -> T a` (or `return`)
`μ :: T (T a) -> T a` (or `join`).  
```
eval . return = id
a . join = eval . fmap eval
```
That makes F-algebras and T-algebras different!
 
T-algebras form Eilenberg-Moore category with morphisms
```
h :: (A, evalA : T a -> a) -> (B, evalB : T b -> b)
h :: a -> b

h . evalA = evalB . fmap h
```
These are the homomorphisms of algebras and the definition is the same as for F-algebras. 


__Free-forgetful adjunction and monad algebra__
There is an interesting fact (see schoolofhaskell link above) that expands on the List example in the book.
The list example in the book points out how T-algebra based on the List monad can be viewed as
```
foldr :: (a -> a -> a) -> a -> [a] -> a
foldr f z = ...
```
where `(a, f, z)` is a monoid.
The T-algebras of the List monad are monoids, 
also the algebra homomorphisms (Eilenberg-Moore category morphisms for List) are monoid homomorphisms.

The schoolofhaskell post links free-forgetful adjunction and T-algebra. 
In free-forgetful adjunction F -| U where U : C -> D 
the category of monad algebras of the functor UF (we know UF is a Monad) is equivalent to the category C!

In the case of List monad, we get D=Set, C=__Mon__ so the category of monad algebras is equivalent to __Mon__ 
(the category of monoids).
That suggest that monad algebras for the List functor have monoid structure, which is consistent
with the example in the book.
 

__F-algebra vs T-algebra__
Can be very different, for example F-algebra for List does not have monoid structure.
For example, List monad algebras are monoids, but functor algebras do not have to be. 
For example, initial algebra of the List functor is isomorphic to:  

> data RoseTree = Node [RoseTree]

and that is not a monoid. 

Recall:
```
data List a = Nil | Cons a (List a)
newtype Fix f = Fix (f (Fix f))
```
If I was to define:
```
type RoseTree = Fix List
```
then the isomorphism would be just renaming Fix to Node:
```
RoseTree =
Fix List =
Fix (List (Fix List)) =
Fix (List (RoseTree)) ~=
Node (List (RoseTree))
```

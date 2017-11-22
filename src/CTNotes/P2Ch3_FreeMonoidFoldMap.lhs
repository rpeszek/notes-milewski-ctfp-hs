|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch3_FreeMonoidFoldMap

This note explains factorization in free construction of monoid using Haskell. It is the `foldMap`! 

This note explores 
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 2. Ch.3 Free Monoids](https://bartoszmilewski.com/2015/07/21/free-monoids/).


> module CTNotes.P2Ch3_FreeMonoidFoldMap where
> import Data.Foldable (foldMap)
> import Data.Monoid

After reading [Chapter 3](https://bartoszmilewski.com/2015/07/21/free-monoids/) 
about free construction of monoid I wrote this:

> factorize :: Monoid m => (a -> m) -> [a] -> m
> factorize q  = foldr mappend mempty . map q

Hmm, that does look familiar.  This is exactly `foldMap` (even has the same implementation).
```
foldMap :: Monoid m => (a -> m) -> [a] -> m
```
Read this as:  Given monoid m, a type `a` that defines monoid generators, 
and function `q :: a -> m` that identifies these generators in `m`, I can obtain 
a factorizing homomorphisms `[a] -> m` from the list monoid.  
This is the essence of monoid free construction and shows that list is the free monoid. 

Note 1: Not so fast, the factorizing homomorphisms needs to be unique and, well, it needs to be a
homomorphisms. These things are outside of what Haskell type system can express and are 
proof obligations.  
Note 2: The list type should really contain finite lists only, but I am ignoring it.  
Note 3: Because `mappend` is associative left associative `foldl` would do too. 

Proof obligations
-----------------
__Homomorphism__  
Morphism `foldMap q :: [a] ->  m` is homomorphic by construction.  
To be more diligent, here is a proof:
We need to show
```
foldMap q [] == mempty  -- (1)
foldMap q (xs ++ ys) == (foldMap q xs) `mappend` (foldMap q ys) -- (2)
```
(1) is trivial.  
One way to show (2) is to use induction on the size of `xs`.
That is is trivial for `xs=[]`.  For non-empty `xs` it directly follows from the 
definition of `foldr`
```
foldMap q ((x:xs) ++ ys) == - implementation def
foldr mappend mempty . map q ( (x:xs) ++ ys) == -- def of foldr
(q x) `mappend` (foldr mappend mempty . map q ( xs ++ ys)) == -- induction
(q x) `mappend` ((foldMap q xs) `mappend` (foldMap q ys)) == -- mappend associativity
((q x) `mappend` (foldMap q xs)) `mappend` (foldMap q ys)) == -- def of foldr
(foldMap q (x:xs)) `mappend` (foldMap q ys)
```
_square box_

__Uniquness__  
follows from properties of monoids.  
Assume that there is another homomorphisms  

> factorize' :: Monoid m => (a -> m) -> [a] -> m
> factorize' q = undefined

that factorizes `q`.  
We know that both need to act the same on single element lists (requirement of this free construction)
```
foldMap    q [ax] = q ax
factorize' q [ax] = q ax
```
And both need to match on empty lists too.
The proof is, again, a simple induction on the size of the list
```
factorize' q x:xs == -- homomorphism
(factorize' q [x]) `mappend` (factorize' q xs) == -- induction
(factorize' q [x]) `mappend` (foldMap q xs) == -- free construction requirement
(foldMap q [x]) `mappend` (foldMap q xs) == -- foldMap q is homomorphisms 
foldMap q x:xs
```

Note: writing this code is a garden path walk too. We could have made some 
equivalent choices by using left associative `foldl` instead of right associative `foldr`
but these end up superficial (`mappend` associativity).
 

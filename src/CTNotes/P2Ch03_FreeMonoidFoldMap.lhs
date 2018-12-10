|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch03_FreeMonoidFoldMap

This note explains factorization in the free construction of monoid using Haskell. It is the `foldMap`! 

This note explores 
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 2. Ch.3 Free Monoids](https://bartoszmilewski.com/2015/07/21/free-monoids/).


> module CTNotes.P2Ch03_FreeMonoidFoldMap where
> import Data.Foldable (foldMap)
> import Data.Monoid

After reading [Chapter 3](https://bartoszmilewski.com/2015/07/21/free-monoids/) 
about free construction of monoid I wrote this:

> factorize :: Monoid m => (a -> m) -> [a] -> m
> factorize q  = foldr mappend mempty . map q

Hmm, that does look familiar.  This is `foldMap` 
(ignoring the more general foldable `t` but keeping the same implementation).
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
Note 3: Because `mappend` is associative, left associative `foldl` would do too. 

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

__Uniqueness__  
follows from properties of monoids.  
Assume that there is another homomorphisms  

> factorize' :: Monoid m => (a -> m) -> [a] -> m
> factorize' q = undefined

that factorizes `q`.  
We know that both need to act the same on single element lists 
(This is the requirement of the free construction,
notice that, what book calls, `p` is the obvious embedding `p :: a -> [a]` 
that creates single element list, U is the identity functor, types `X-ray` themselves)
```
foldMap    q [ax] = q ax -- from implementation
factorize' q [ax] = q ax -- from construction
```
And both need to match on empty lists too.
The proof is, again, a simple induction on the size of the list
```
factorize' q x:xs == -- homomorphism
(factorize' q [x]) `mappend` (factorize' q xs) == -- induction
(factorize' q [x]) `mappend` (foldMap q xs) == -- free construction requirement
(foldMap q [x]) `mappend` (foldMap q xs) == -- foldMap q is homomorphism 
foldMap q x:xs
```

__square box__

Note 1: writing this code is a garden path walk. We could have made some 
equivalent choices by using left associative `foldl` instead of right associative `foldr`
but these end up superficial (`mappend` associativity).
 
Note 2: Given generators, free monoid is unique up to isomorphism.  This follows directly
from the uniqueness of the factorizing homomorphism.  


Is List the only foldable that is also a monoid?
------------------------------------------------
Answer: __NO__   
`foldMap` is what defines Foldable also `foldMap` embodies the free construction of monoid. 
That would suggest that if we impose additional constraint 
```
factorizeFoldable :: (Monoid m, Monoid (t a), Functor t) => (a -> m) -> t a -> m
factorizeFoldable q = foldr mappend mempty . fmap q
```
the resulting morphism `t a -> m` would be a homomorphism and we would satisfy free construction.
Because of uniqueness of free construction, `t` would have to be isomorphic to `[]`. 

What breaks in this argument is that we cannot prove uniqueness of factorization 
for a non-list `t`. 
Types are sometimes not everything. 

Counterexample: 

> data TreeWithInorderTraversal a = Leaf a 
>                                   | Split {left:: TreeWithInorderTraversal a, right:: TreeWithInorderTraversal a} 
>                                   | Flat [a]
>
> traverseInorder :: TreeWithInorderTraversal a -> [a]
> traverseInorder = undefined

Deriving `Functor` and `Foldable` on this is straightforward 
(Coproduct of foldables is foldable, Coproduct of functors is functor, etc).

> instance Monoid (TreeWithInorderTraversal a) where
>   mempty = Flat []
>   tree1 `mappend` tree2 = Flat (traverseInorder tree1 ++ traverseInorder tree2) 

monoid laws follow from the monoid properties of the list.  
This structure is not a List and is not a free monoid, 
but it is an honest `Monoid` and it is an honest `Foldable`. 

Adjunction
----------
Free monoid is described by the free-forgetful adjunction between the (left adjoint) List functor and the 
forgetful functor U (here `Identity`).
`foldMap :: (a -> m) -> [a] -> m` is the non trivial natural isomorphism (`rightAdjunct`) in that adjunction. 

Not a real code since the `Adjunction` typeclass works on Hask endofunctors: 
```
instance Adjunction [] Identity where
   leftAdjunct  :: ([x] -> m) -> x -> Identity m
   leftAdjunct f x = Identity (f [x])
   rightAdjunct :: (x -> Identity m) -> [x] -> m
   rightAdjunct f = foldMap (runIdentity . f)
```

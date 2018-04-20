|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch15a_Spans

Notes about CTFP Part 3 Chapter 12. Span bicategory
===================================================

Note about the category of spans described in [chapter 15](https://bartoszmilewski.com/2017/09/06/monads-monoids-and-categories/).
It provides supporting conceptual code in Haskell. 
These notes use the concept of pullback which is not directly expressible in Haskell's language (and, probably, lead to undecidable
problems).  

> {-# LANGUAGE MultiParamTypeClasses
>   , ExistentialQuantification
>   , FlexibleContexts
>   , ScopedTypeVariables 
>   #-}
>
> module CTNotes.P3Ch15a_Spans where

_Span_ bicategory
-----------------

> data Cell0 a = Cell0 a
> data Cell1 x a b = Cell1 (x -> a) (x -> b)
> data Cell2 x y a b = Cell2 (x -> y)

0-cells are Haskell types.  
1-cells are spans consisting of 2 morphisms (legs) from a common object x (support object/apex).  
2-cells are morphisms between apex objects that result in commuting diagrams involving legs.  
```
             z
          /  |  \
         /   |   \
        a <- x -> b 
```
Type `Cell1 x a b` represents a morphism between `Cell0 a` and `Cell0 b`.
Type `Cell2 x y a b` represents a natural transformation between `Cell1 x a b` and `Cell2 x a b`
where a and b are the same for both 1-cells.
This note is focused on 1-cells.


`Cell1`-s as morphisms of `Cell0`-s
-----------------------------------

__Identity__  
The identity morphism is:

> idm :: Cell1 a a a
> idm = Cell1 id id

__Composition__  
Composition of spans needs the notion of pullback.  
To approximate pullbacks in Haskell, I use this type constructor 

> data Pullback x y a = forall z . Pullback z (z -> x) (z -> y)

This type represents some type `z` representing the pullback object and 2 morphisms `p1::z -> x`
and `p2::z -> y` which complete the pullback construction of given functions 
`f:: x -> a` and `g:: y -> a`.

For sets, pullback of `f` and `g` is often defined as a subset of elements in `(x,y)`:  
`[(xa,ya) | xa <- x, ya <- y, f xa == g ya]`.  
The above definition is consistent with this approach:

> class Subset s a where
>   inject :: s -> a
>
> instance Subset (Pullback x y b) (x,y) where
>   inject (Pullback z f1 f2) = (f1 z, f2 z)

In this approach, Pullback of `x` and `y` on top of `b` is viewed as some type `z` 
together with injection of z into (x,y).

The composition of 1-cells can be defined in Haskell as:

> comp :: forall x y a b c .  Cell1 y b c -> Cell1 x a b -> Cell1 (Pullback x y b) a c
> (Cell1 g1 g2) `comp`  (Cell1 f1 f2) 
>                 = Cell1 h1 h2
>                   where 
>                      h1 :: Pullback x y b -> a
>                      h1 (Pullback z p1 _) =  f1 . p1 $ z
>                      h2 :: Pullback x y b -> c
>                      h2 (Pullback z _ p2)  = g2 . p2 $ z


Proofs of Category Laws
-----------------------

Notice that other than the type itself, pullback is not used in the above implementation of `comp`. 
However, pullbacks are needed in verifying category laws. 
For the category of spans these laws hold only up to isomorphism.   
(In following diagrams vertical arrows are implicitly pointing down.)

__Right Identity__  
Need to show existence of isomorphism:
```
idm 'comp' Cell1 x a b  ~= Cell1 x a b 
```
The proof follows directly from the uniqueness of universal construction.

I have the following diagram:
```
            x
         /id   \f
       x         b 
     /   \f   /id  \
   a        b        b 
   
Cell1 x a b |  idm 
Cell1 _ _ f
```
Note this diagram satisfies `f . id == id . f` and provides a valid pullback candidate for `f` and `id`.
Let z be any other pullback candidate:
```
            z
         /p1  \p2
       x         b 
         \f   /id  
            b        
```
It suffices to show that we can factorize `h :: z -> x`.  
Take `h = p1`.  The following diagram commutes proving the factorization.

```
           z
       /   |   \   
   p1 /    |p1  \ p2
     /     |     \
    /  id  |   f  \
   x  <-   x  ->   b
    \             /
     \ f         / id
      \         /
           b
           
```

__Left Identity__  follows from similar arguments due to symmetry.

__Associativity__  
Using `z = x ×a y` to represent following pullback
(names of morphisms are ignored in the notation and in this proof).
```
  z --> y 
  |     |
  |     |
  x --> a      
```

The proof follows from what is called associativity property of pullbacks:
Consider a commutative diagram (in any category)
```
   a  ---->  b  -----> c
   |         |         |
   |         |         |
   |         |         |
   d  ---->  e  -----> f
```
Suppose the right-hand inner square is a pullback, then:
the square on the left is a pullback if and only if the outer square is.
(This means that I can collapse adjacent pullback square diagrams to get a pullback diagram.)
(Ref: https://ncatlab.org/nlab/show/pullback Proposition 3, or Borceux categorical algebra handbook vol 1)

Consider this diagram where each square is a pullback:
```
   r ----> b ×e c  -----> c
   |         |            |
   |         |            |
   |         |            |
 a ×d b -->  b  --------> e
   |         |            
   |         |          
   |         |           
   a  ---->  d      
```
Composing horizontal arrows we get a pullback
```
   r ---->   c
   |         |            
   |         |  
   |         |  
 a ×d b -->  e

```
similarity composing vertical arrows there is a pullback:
```
   r ----> b ×e c 
   |         |            
   |         |          
   |         |           
   a  ---->  d      
```
yielding isomorphisms `(a ×d b) ×e c -> r` and `r -> a ×d (b ×e c)`. 
Combining these shows associativity up to isomorphism.


Fun Note
--------
Trying to come up with Haskell code for this note I got the following ghc error:

```
    • My brain just exploded
      I can't handle pattern bindings for existential or GADT data constructors.
      Instead, use a case-expression, or do-notation, to unpack the constructor.
```

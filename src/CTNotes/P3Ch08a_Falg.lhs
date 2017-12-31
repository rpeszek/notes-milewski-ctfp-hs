|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch08a_Falg

__Work-in-progress__

> {-# LANGUAGE Rank2Types #-}
>
> module CTNotes.P3Ch08a_Falg where

Fix/Unfix Fold/Unfold iso and equi-recusive types
-------------------------------------------------

According to TAPL ML languages are iso-recursive. That means that the the language will use fold/unfold
implicitly (part of operational semantics) or programs will be explicitly annotated with fold/unfold instructions. 
It is interesting that 
"In languages in the ML family, for example, every datatype definition implicitly introduces a recursive type."
(TAPL book)

This is cool, so if I type 

```
data List a = Nil | Cons a (List a)
```

the compiler can be changing it to something like (quoted from TAPL) under the hood  
```
NatList = μX. <nil:Unit, cons:{Nat,X}>;
-- operational semantics
unfold[μX.T] : μX.T -> [X →μX.T] T 
fold[μX.T] : [X →μX.T] T -> μX.T

-- unfolded form:
NLBody = <nil:Unit, cons:{Nat,NatList}>;

nil = fold [NatList] (<nil=unit> as NLBody); 
cons = λn:Nat.λl:NatList. fold [NatList] <cons={n,l}> as NLBody;

isnil = λl:NatList. case unfold [NatList] l of <nil=u>⇒true | <cons=p>⇒false; 
tail =λl:NatList. case unfold [NatList] l of <nil=u>⇒l | <cons=p>⇒p.2;
-- etc
```

Here is Haskell version

> newtype Fix f = Fix { unFix :: f (Fix f)}
>
> data ListF a x = Nil | Cons a x
> type ListFx a = Fix (ListF a)
>
> nil :: ListFx a
> nil = Fix Nil
> cons :: a -> ListFx a -> ListFx a
> cons a list = Fix (Cons a list)
> 
> isnil :: ListFx a -> Bool
> isnil list = case unFix list of 
>      Nil -> True
>      Cons _ _ -> False
> tail' :: ListFx a  -> ListFx a 
> tail' list = case unFix list of
>      Nil -> list
>      Cons _ x -> x

Language operational semantics basically applies or removes a wrapping layer.
iso-recursion works as Fix works on corresponding Functor types and languages can do the `Fix` trick under the hood.
Two forces in programming: construction and deconstruction (patter matching) are represented as `Fix` and `unFix` 
(in TAPL terms 'fold' and unfold).

__Long term TODO__:  TAPL implements equi-recursion using co-induction based on monotone functions.  
It would be cool to understand how equi-recursion plays out using more CT approach. 
On high level things are very similar, we have least and greatest fixpoints for example.  

__Recap__   
It is short of amazing that category theory provides another interpretation of recursive types.
Lambek theorem says that among F-algerbras `F a -> a` if there is an initial one its carrier type will 
be the fix point of `F`: `F i ~= i`.  This is the equi-recursive take on `μ`. 


Initial algebra, uniqueness
---------------------------
Ref: [Wadler, Recursive Types for Free](http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt) 

Considering type constructors F x where x is appears in positive position (as it should for covariant functor),
the least fixpoint of F can, actually, be expressed in System F (without recursion).
Using Haskell these map to:

> data LFix f = LFix (forall x. (f x -> x) -> x)

Using these functions

> fold:: forall x f. (f x -> x) -> LFix f -> x
> fold = \k (LFix t) -> t k
>
> in':: Functor f => f (LFix f) -> LFix f
> in' s = LFix $ \k -> k (fmap (fold k) s)

This diagrams commutes:
```
T = LFix F
	                     in            
	             F T ----------> T   
	              |              |    
	              |              |    
   F (fold X k) |              | fold X k
	              |              |
	              |              |
	             F X ----------> X
	                      k
```
And it turns out that uniqueness is a consequence of parametrically. 
Using generic CT arguments, uniqueness (the fact that (T, in) is initial) is equivalent to following
2 conditions (using ref numbers 3 and 4 to match the paper):

```
	            k                                fold X k
	    F X ----------> X                    T -----------> X
	     |              |                    |              |
	     |              |                    |              |
   F h |              | h    implies    id |              | h    (#3)
	     |              |                    |              |
	     |              |                    |              |
	    F X' ---------> X'                   T -----------> X' .
	            k'                              fold X' k'
--and 

fold T in  =  id.                                                (#4)
```
and, for System F, (#4) is automatic!

Quoting the paper:
"Law (#3) does not follow from the reduction laws of polymorphic lambda
calculus, and indeed there are models that do not satisfy it.  But this
law is satisfied in many models, including all those having the
property of PARAMETRICITY ...
'Theorem for Free' derived from the type of 'fold' is just this
law."


Finite Cats Example
-------------------
Considering the `A -> B => C` example from `N_P1Ch03b_FiniteCats`.
Since not trivial morphisms are never invertible Lambek theorem says
that initial F-algerbra in this category (if exists) will need to always be based 
on `id` morphism.

Functor example
```
     MorphAB     MorphBCi (i=1,2)
  A   ---->   B  =====>  C
  |         /           /
  |       /           /
  |     /           /             Functor F
  |   /           /
  | /           /
  A           B          C

F MorphAB = ID_A
F MorphBCi = MorphAB
```
Note given choices of `F B` and `F C`,  `F A` can only go to A.  
Possible elements in F-algebra for F (all work)
```
(A, ID) - Initial
(B, MorphAB)
(C, MorphBC1)
(C, MorphBC2)
```

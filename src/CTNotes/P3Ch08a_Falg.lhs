|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch08a_Falg

This note explores relationship between F-algebra and iso-recursion,
Wadler's paper 'Recursive Types for Free', and
provides examples of F-Algebras in `A->B=>C` category from [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats).

Book Ref: [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)
[P3 Ch8. F-Algebras](https://bartoszmilewski.com/2017/02/28/f-algebras/).


> {-# LANGUAGE Rank2Types
>  , ExistentialQuantification 
>  #-}
>
> module CTNotes.P3Ch08a_Falg where


Fix/Unfix Fold/Unfold iso and equi-recusive types
-------------------------------------------------
According to the [TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/) book all ML languages are iso-recursive. 
This means that the the language will use fold/unfold implicitly (as a part of operational semantics) or 
programs will be explicitly annotated with fold/unfold instructions.   
Interesting quote: 
"In languages in the ML family, for example, every datatype definition implicitly introduces a recursive type."
(TAPL book)

So if I type 

```
data List a = Nil | Cons a (List a)
```

the compiler will change it to something like (quoted from TAPL):  
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

Here is Haskell version of that transformation:

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

So iso-recursion works the same way as the Fix type!
Two forces of programming: construction and deconstruction (patter matching) are represented as `Fix` and `unFix` 
(in TAPL terms 'fold' and unfold).

__Long term TODO__:  TAPL implements equi-recursion using co-induction based on monotone functions.  
It would be cool to understand how equi-recursion plays out using more CT approach. 
On high level things are very similar, we have the least and greatest fixpoints for example.  

__Recap__   
It is short of amazing that category theory aids in understanding of recursive types.
Lambek theorem says that among F-algerbras `F a -> a`, if there is an initial one, its carrier type will 
be the fix point of `F` (`F i ~= i`).  This is exactly the iso-recursive take on `μ`. 


Interesting non-recursive approach. Existence of initial algebra.
-----------------------------------------------------------------
Ref: [Wadler, Recursive Types for Free](http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt) 

Considering type constructors __F x__ containing __x__ in positive position only 
(as it should for covariant functor),
the least fixpoint of F can be expressed in System F (without recursion).
Using Haskell this maps to:

> data LFix f = LFix (forall x. (f x -> x) -> x)

These functions

> fold:: forall x f. (f x -> x) -> LFix f -> x
> fold = \k (LFix t) -> t k
>
> in':: Functor f => f (LFix f) -> LFix f
> in' s = LFix $ \k -> k (fmap (fold k) s)

form commuting diagram
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
__T__ is carrier and `in` is evaluator of an F-algebra from which there is a map, `fold X k`, to every other F-algebra.  
But is it really initial (is that map to any other object unique)? 
And it turns out that this uniqueness (the fact that __(T,in)__ is initial) is a consequence of parametricity.  
Using generic CT arguments, this is equivalent to following 2 conditions (using ref numbers 3 and 4 to match the paper):

```
             k                                 fold X k
      F X ----------> X                    T -----------> X
       |              |                    |              |
       |              |                    |              |
   F h |              | h    implies    id |              | h    (#3)
       |              |                    |              |
       |              |                    |              |
      F X' ---------> X'                   T -----------> X' .
             k'                               fold X' k'
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
Considering the `A -> B => C` example from [N_P1Ch03b_FiniteCats](N_P1Ch03b_FiniteCats).
Since not trivial morphisms in this category are not invertible, Lambek theorem says
that initial F-algerbra in this category (if exists) will need to always be based 
on `id` morphism.

Functor example
```
     MorphAB     MorphBCi (i=1,2)
  A   ---->   B  =====>  C
  |         /           /                    |
  |       /           /                      |
  |     /           /             functor F  |
  |   /           /                          |
  | /           /                           \ /
  A           B          C

F MorphAB = ID_A
F MorphBCi = MorphAB
```
To keep consistent with the book, in this section, I use `(->)` as morphism in `A -> B => C`,
as if it was pseudo-defined like so:
```
type (->) = P1Ch03b_FiniteCats.HomeSet
```
(TODO makes sense to disambiguate)

Possible F-algebras `(o, m)` such that `m :: F o -> o`
```
(A, ID) - Initial
(B, MorphAB)
(C, MorphBC1)
(C, MorphBC2)
```
It is also interesting to note that for any functor `F`, F-algebra `F A -> A`
is only possible if F A = A.  
We have more choices for Fs that allow algebras `F B -> B` or `F C -> C`.


More about Recursive Types
--------------------------
See package 
[recursion-schemes](https://hackage.haskell.org/package/recursion-schemes-5.0.2/docs/Data-Functor-Foldable.html)  
See also
https://stackoverflow.com/questions/45580858/what-is-the-difference-between-fix-mu-and-nu-in-ed-kmetts-recursion-scheme-pac

We have seen
```
newtype Fix f = Fix (f (Fix f))
data LFix f = LFix (forall x. (f x -> x) -> x)
```
There is also existentially formed greatest fixpoint

> data GFix f = forall a . GFix ((a -> f a) -> a)

all are supposed to be isomorphic in Haskell.

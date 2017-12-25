|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch08a_Falg

__ Very much work-in-progress __

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


TODO Initial algebra, uniqueness
--------------------------------
[Wadler, Recursive Types for Free](http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt) 

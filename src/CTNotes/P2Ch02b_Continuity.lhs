|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch02b_Continuity

CTFP Part 2 Chapter 1. Limits and Colimits - continuous functors 
================================================================

This note explores last section of
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Part 2. Ch.1 Limits and Colimits](https://bartoszmilewski.com/2015/04/15/limits-and-colimits/).

Continuity condition is appears to be super strong. It requires that all kinds of diagrams commute.
This note shows that functors are mostly not continuous.

> {-# LANGUAGE GADTs 
>  , DataKinds 
>  , KindSignatures 
>  , TypeOperators 
>  , FlexibleInstances 
>  #-}
>
> module CTNotes.P2Ch02b_Continuity where
> import GHC.TypeLits
> import Data.Functor.Const (Const(..))
> import CTNotes.P1Ch07_Functors_Composition (Iso(..))

__Definition:__ Functor F :: C -> B is continuous if Lim (F ∘ D) ~= F (Lim D) for every diagram D :: I -> C.  

It is probably not possible to express this definition in Haskell.  Very few limit constructions
are easily expressed.  Fortunately, the limit of `2 -> Hask` functor is the pair type `(,)`.
That gives me one diagram I can easily use to check the continuity.  
Continuous functors need to satisfy  
 F (a, b) ~= (F a, F b):

> class (Functor f) => CommutesWithPair f where
>     commuteProof :: Iso (f (a,b)) (f a, f b)
> instance CommutesWithPair ((->) r) where
>     commuteProof = IsoProof (\f -> (fst . f, snd . f)) (\(fa, fb) -> (\r -> (fa r, fb r)))


CTFP states that the `(->)` profunctor is continuous (maps colimits to limits in first type variable
and limit to limits in the second).  This seems to be a very strong property considering that the functor needs to 
commute with any diagram not just the product `(,)`.

Still, just checking the Pair constructor eliminates lots of functors from that game!

The following functors apparently are not continuous because we simply can count inhabitants of (compare cardinality of) 
`f (Bool, Bool)` vs `(f Bool, f Bool)` or even `f ((), ())` vs `(f (), f ())`: 

- `Const a` - for `a` with > 1 inhabitants
- `Maybe`
- `Either Err`

This provides a perfect excuse to do some type level programming. I will prove this using Haskell type checker!  
First, I need to develop ability to calculate type cardinalities (count values that inhabit the type).   
(`KindSignatures` allows to define type level variables of kind `Nat`, 
`GHC.TypeLits` allow to use type level number literals, `<=`, `+`, `*` are type families that work on 
type level numbers)  

> data TypeCardinality a (n :: Nat) = TypeCardinality
>
> boolCard :: TypeCardinality Bool 2
> boolCard = TypeCardinality
>
> unitCard :: TypeCardinality () 1
> unitCard = TypeCardinality
>
> constCard ::  TypeCardinality a n -> TypeCardinality (Const a b) n
> constCard _ = TypeCardinality
>
> pairCard :: TypeCardinality a n -> TypeCardinality b m -> TypeCardinality (a, b) (n * m)
> pairCard _ _ = TypeCardinality
>
> maybeCard :: TypeCardinality a n -> TypeCardinality (Maybe a) (1 + n)
> maybeCard _ = TypeCardinality
>
> eitherCard :: TypeCardinality b n -> TypeCardinality a m -> TypeCardinality (Either b a) (n + m)
> eitherCard _ _ = TypeCardinality

The following GADT (`NotContinuousEv`) encodes a reason why type constructor `f` is not continuous. 
It has one constructor because I only came up with one method for generating counter examples.  
It type checks that the cardinalities are actually different. 
`GADTs` pragma is needed for 'other' things like existential quantification, 
integration with `DataKinds`, and typeclass constraints 
(otherwise I could have defined `NotContinuousEv` as a regular ADT).  
Existential quantification is perfect for writing counter examples.  I can just pick a type that has mismatch.  

> data NotContinuousEv (f :: * -> *) where 
>    CardinalityMismatch :: (1 + n1 <= n2) => 
>            TypeCardinality (f (a,b)) n1 -> 
>            TypeCardinality (f a, f b) n2 -> 
>            NotContinuousEv f
> 
> class (Functor f) => NotContinuous f where
>    counterExample :: NotContinuousEv f

Proof that `Const Bool` is not continuous simply compares cardinalities for `Const Bool (a, b)` with `(Const Bool a, Const Bool b)`:

> instance NotContinuous (Const Bool) where
>    counterExample = CardinalityMismatch 
>                        (constCard boolCard) 
>                        (pairCard (constCard boolCard) (constCard boolCard)) 

Similarly, we get different cardinalities for `Maybe (Unit, Unit)` vs `(Maybe Unit, Maybe Unit)`

> instance NotContinuous Maybe where
>    counterExample = CardinalityMismatch 
>                        (maybeCard $ pairCard unitCard unitCard) 
>                        (pairCard (maybeCard unitCard) (maybeCard unitCard)) 

and we can expect the same for `Either` since `Either ()` is isomorphic to `Maybe`.  

> instance NotContinuous (Either ()) where
>    counterExample = CardinalityMismatch 
>                        (eitherCard unitCard $ pairCard unitCard unitCard) 
>                        (pairCard (eitherCard unitCard unitCard) (eitherCard unitCard unitCard)) 

GHC type checker knows that 2 < 4 (1 + 2 <= 4 to be exact).  This is far from being a proof assistant but I still 
find it amazing. 

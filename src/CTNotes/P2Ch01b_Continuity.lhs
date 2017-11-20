|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch01b_Continuity

Work in progress

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE FlexibleInstances #-}
>
> module CTNotes.P2Ch01b_Continuity where
> import GHC.TypeLits
> import Data.Proxy
> import Data.Functor.Const (Const(..))
> import CTNotes.P1Ch07_Functors_Composition (Iso(..))

Def: F :: C -> B is continuous if Lim (F ∘ D) ~= F (Lim D) for every diagram D :: I -> C.  
It is probably not possible to express this definition in Haskell.  Very few limit constructions
are easily expressed.  Fortunately, the limit of `2 -> Hask` functor is the pair type `(,)`.
That gives me one diagram I can easily use to check the continuity.  Continuous functors need to satisfy  
 F (a, b) ~= (F a, F b):

> class (Functor f) => CommutesWithIso f where
>     commuteProof :: Iso (f (a,b)) (f a, f b)
> instance CommutesWithIso ((->) r) where
>     commuteProof = IsoProof (\f -> (fst . f, snd . f)) (\(fa, fb) -> (\r -> (fa r, fb r)))


CTFP states that the `(->)` profunctor is continuous (maps colimits to limits in first type variable
and limit to limits in the second).  This seems a very strong property considering the the functor needs to 
commute with any diagram not just the product `(,)`.

Still, just the product check eliminates lots of Functors from that game!
The following functors apparently are not continuous because we simply can count inhabitants of `f (Bool, Bool)`
vs `(f Bool, f Bool)` or even `f ((), ())` vs `(f (), f ())`
- `Const a` - for `a` with > 1 inhabitants
- `Maybe`
- `Either Err`

I will prove this with GHC type solver!  
First I need to develop ability to calculate type cardinalities on the type level.

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
> maybeCard :: TypeCardinality a n -> TypeCardinality (Maybe a) (n + 1)
> maybeCard _ = TypeCardinality
>
> eitherCard :: TypeCardinality b n -> TypeCardinality a m -> TypeCardinality (Either b a) (n + m)
> eitherCard _ _ = TypeCardinality

This GADT encodes a reason why type constructor `f` is not continuous. Has one constructor because I came up with one method for 
generating counter examples:

> data NotContinuousEv (f :: * -> *) where 
>    CardinalityMismatch :: (n1 + 1 <= n2) => TypeCardinality (f (a,b)) n1 -> TypeCardinality (f a, f b) n2 -> NotContinuousEv f
> 
> class (Functor f) => NotContinuous f where
>    counterExample :: NotContinuousEv f

Proof that `Const Bool` is not continuous,  
this simply compares (at type level) cardinalities for `Const Bool (a, b)` with `(Const Bool a, Const Bool b)`:

> instance NotContinuous (Const Bool) where
>    counterExample = CardinalityMismatch (constCard boolCard) (pairCard (constCard boolCard) (constCard boolCard)) 

TODO finish this for other types

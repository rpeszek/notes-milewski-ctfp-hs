|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P2Ch01b_Continuity

Work in progress

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE KindSignatures #-}
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
and limit to limits in the second).  This is very strong property considering the the functor needs to 
commute with any diagram not just the product `(,)`.

Still, just the product check elimiates lots of Functors from that game!
The following functors apparently are not continuous because we simply can count inhabitants of `f (Bool, Bool)`
vs `(f Bool, f Bool)` or even `f ((), ())` vs `(f (), f ())`
- `Const a` - for `a` with > 1 inhabitants
- `Maybe`
- `Either Err`

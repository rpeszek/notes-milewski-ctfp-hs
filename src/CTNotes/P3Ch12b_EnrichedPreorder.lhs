|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch12b_EnrichedPreorder

Notes about CTFP Part 3 Chapter 12. Enhanced Categories. Preorder Example.
==========================================================================

Notes about Preorder example as an enriched category.
See how far I can get implementing it in Haskell.
The goal here is to internalize enhanced categories trying to write Haskell. 
I also think that this approach could go places when dependent types become 
easier and better supported. 

Book Ref: [Part 3 Chapter 12, enhanced categories](https://bartoszmilewski.com/2017/05/13/enriched-categories)

> {-# LANGUAGE GADTs 
>   ,  DataKinds 
>   ,  KindSignatures 
>   ,  TypeOperators 
>   ,  TypeFamilies 
>   ,  FlexibleInstances 
>   ,  PolyKinds 
>   ,  AllowAmbiguousTypes  -- needed in bitmap signature
>   ,  UndecidableInstances  -- needed in type level If
>  --  , TypeFamilyDependencies  -- attempt to allow associator signature
>   ,  InstanceSigs
>   ,  MultiParamTypeClasses
>   ,  TypeInType
>   ,  ScopedTypeVariables 
>  #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> module CTNotes.P3Ch12b_EnrichedPreorder where
> import GHC.TypeLits
> import Control.Category
> import Prelude (undefined, (+), Bool(True, False))
> import Data.Kind (Type)


Construction of Enhanced Preorder Category
------------------------------------------
I need to construct a category `V` with two objects representing True and False
of the shape `False -> True` (with one not trivial morphism representing 'absurd' statement)
this category needs to be monoidal.   
Once this is done I will enhance natural numbers `Nat` using `V` to obtain
preorder category with natural numbers as objects and the <= relation as morphisms.

I am using symbol `V` for enhanced category hom-objects.
`V` is itself a category with composition and morphisms (with HomSet).
`DataKinds` are used to make `V` a kind.

> data V = TrueV | FalseV
>
> data VHomSet (a:: V) (b:: V) where
>     MorphIdT :: VHomSet 'TrueV 'TrueV 
>     MorphIdF :: VHomSet 'FalseV 'FalseV 
>     Absurd   :: VHomSet 'FalseV 'TrueV   
>  
> vComp :: VHomSet b c -> VHomSet a b -> VHomSet a c
> vComp MorphIdT mab  = mab      
> vComp MorphIdF mab  = mab      
> vComp mbc MorphIdF =  mbc 

Cool, GHC knows that pattern match `mbc MorphIdT` is redundant!

Control.Category type class expects a polymorphic `id` (`id :: cat a a`) 
which hard to implement for finite cats.

> instance Category VHomSet where
>     id = undefined
>     (.) = vComp

In all fairness, to be a category it should be enough to be able to pick `id` morphism for each type.

> data VObj (a :: V) where
>    TrueRep :: VObj 'TrueV   
>    FalseRep :: VObj 'FalseV
>
> vId :: VObj a -> VHomSet a a
> vId TrueRep = MorphIdT
> vId FalseRep = MorphIdF

Note:
```
ghci> :k VObj
VObj :: V -> *
```
I find that GHC likes code that uses `Type` more than some exotic kind like `V`.
So to make things work, need some representation of elements of kind `k` as regular types. 
`VObj` serves as such representation.

> class HaskEnrichedCategory (obj:: k -> Type) (homset:: k -> k -> Type) where
>   heid :: obj a -> homset a a
>   hecomp :: homset b c -> homset a b -> homset a c
>
> instance HaskEnrichedCategory VObj VHomSet where
>   heid = vId
>   hecomp = vComp

`V` needs to be equipped with a tensor product and the `i` object. 
`(:**:)` is the tensor product in `V` and `i` is `'TrueV`:

> type family (m :: V) :**: (n :: V) :: V where
>    'TrueV :**: 'TrueV = 'TrueV
>    m :**: n = 'FalseV
>
> type I_V = 'TrueV

I use `Nat` kind as the book's `C` category/Set that will be enhanced using `V`

> type family If c t e where
>    If 'True  t e = t
>    If 'False t e = e
>
> type family Preorder (a :: Nat) (b :: Nat) :: V where
>     Preorder m n  = If (m <=? n) 'TrueV 'FalseV

Modifying book notation `C(a,b)` slightly, I have:

> type family C_V (a :: k) (b :: k) :: V
> 
> type instance C_V (a :: Nat) (b :: Nat) = Preorder a b

`Preorder a b` is what book calls `C(a,b)`.


__Composition__   
Quote from the book:
"Let’s have a look at composition. The tensor product of any two objects is 0, unless both of them are 1, in which 
case it’s 1. If it’s 0, then we have two options for the composition morphism: it could be either id0 or 0->1. 
But if it’s 1, then the only option is id1. 
Translating this back to relations, this says that if a <= b and b <= c then a <= c, 
which is exactly the transitivity law we need."

This translates to this code!:

> eComp0 :: VObj (Preorder b c) -> 
>           VObj (Preorder a b) -> 
>           VObj (Preorder a c) -> 
>           VHomSet ((Preorder b c) :**: (Preorder a b)) (Preorder a c) 
> eComp0 TrueRep TrueRep TrueRep = MorphIdT
> eComp0 TrueRep TrueRep FalseRep = undefined  -- this condition should never happen because if f a <= b and b <= c then a <= c
> eComp0 _ FalseRep FalseRep = MorphIdF
> eComp0 FalseRep _ FalseRep = MorphIdF
> eComp0 _ FalseRep TrueRep = Absurd
> eComp0 FalseRep _ TrueRep = Absurd

A more interesting approach would be to use evidence of kind `Nat -> Type` similar to `SNat` below:

> data SNat (n :: Nat) where
>    SZero :: SNat 0
>    SSucc :: SNat n -> SNat (1 + n)

however, this seems not easy

> eComp1 :: SNat a -> SNat b -> SNat c -> VHomSet ((Preorder b c) :**: (Preorder a b)) (Preorder a c) 
> eComp1 SZero SZero SZero = MorphIdT -- compiles
> -- eComp1 (SSucc _) SZero SZero = MorphIdF -- (eComp1 fails)
> eComp1 _ _ _ = undefined

(eComp1 fails) - even this simple pattern match does not compile (TODO - rethink this)
```
      Could not deduce: ('TrueV :**: If (a <=? 0) 'TrueV 'FalseV)
                        ~
                        'FalseV
      from the context: a ~ (1 + n)
```  
    
However, it is simpler for me to move forward with the `eComp1` approach, and this is what
I will do.
   
   

Generalization attempt and CT details
-------------------------------------

Using `NonHaskMonoidal` class from [N_P1Ch08c_BiFunctorNonHask](N_P1Ch08c_BiFunctorNonHask) is hard 
for reasons similar to why it is hard to implement `id` in `instance Category VHomSet`.

The trick is to add `obj :: k -> Type` evidence to the _associator_ and _unitor_ methods.

> class HaskEnrichedCategory obj cat => 
>       Monoidal (obj :: k -> Type) (cat :: k -> k -> Type) where
>    type Tensor (a :: k) (b :: k) :: k
>    type I :: k
>    bimap :: cat a c -> cat b d -> cat ( Tensor a b) (Tensor c d)
>    associator :: obj a -> obj b -> obj c -> cat (Tensor (Tensor a b) c) ( Tensor a (Tensor b c))
>    lunitor :: obj a -> cat (Tensor (I) a) a
>    runitor :: obj a -> cat (Tensor a I) a

moving forward with this approach I can define typeclass for enhanced categories.  
(Note `C` matches the book notation of `C(a,b)`):

> class (Monoidal vobj vcat) => 
>       Enhanced (cobj :: kc -> Type)  (vobj :: kv -> Type) (vcat :: kv -> kv -> Type) where
>    type C (a :: kc) (b :: kc) :: kv
>    ecomp :: cobj a -> cobj b -> cobj c -> vcat (Tensor (C b c) (C a b)) (C a c)

The above construction of preorder category and `Nat` enhanced using `V` satisfies
these constraints!

> instance Monoidal VObj VHomSet where
>    type Tensor a b = a :**: b
>    type I = 'TrueV
>    bimap :: VHomSet a c -> VHomSet b d -> VHomSet (a :**: b) (c :**: d)
>    bimap Absurd Absurd  = Absurd
>    bimap MorphIdT Absurd  = Absurd
>    bimap Absurd MorphIdT = Absurd
>    bimap MorphIdT MorphIdT = MorphIdT
>    -- bimap _ _ = MorphIdF  - (0)
>    bimap _ MorphIdF = MorphIdF
>    bimap MorphIdF _ = MorphIdF
>    associator :: VObj a -> VObj b -> VObj c -> VHomSet ((a :**: b) :**: c) ( a :**: ( b :**: c)) -- (1)
>    associator TrueRep TrueRep TrueRep = MorphIdT  
>    -- associator _ _ _ = MorphIdF -- (2)
>    associator _ _ FalseRep = MorphIdF  
>    associator _ FalseRep _ = MorphIdF  
>    associator FalseRep _ _ = MorphIdF  
>    lunitor :: VObj a -> VHomSet ('TrueV :**: a) a
>    lunitor TrueRep = MorphIdT  -- (3)
>    lunitor FalseRep = MorphIdF  
>    runitor :: VObj a -> VHomSet (a :**: 'TrueV) a
>    runitor TrueRep = MorphIdT  -- (3)
>    runitor FalseRep = MorphIdF  

Some interesting peculiarities and additional reasons why I needed conversion
to regular types `vobj :: kv -> Type`:   
(0) -  does not work and pattern match needs to be spelled out.  
_Note about bimap implementation:_ The only way to get Absurd is to have `a :**: b` False and `c :**: d` True.
that implies that `c` and `d` are True and `a` or `b` are False.
The only way to get MorphIdT is if both `(a :**: b)` and `(c :**: d)` are True 
which means all `a`, `b`, `c` and `d` are True.  

(1) - without `VObj a` evidence the above type signature causes compiler error:   
‘:**:’ is a type function, and may not be injective, using `TypeFamilyDependencies` pragma does not help.

(2) - similarly to (0) I have to spell out the pattern match more

(3, 4) - ghc does not know how prove that 
`VHomSet ('TrueV :**: a) a` is the same as `VHomSet a a` making it not implementable 
without `VObj a` Hask `obj` evidence.
Even if I had a polymorphic `id` function
```
lunitor = id 
```
I would get this compiler error:
```
    Expected type: VHomSet ('TrueV :**: a) a
    Actual type: VHomSet a a
```

Finally, I have:

> instance Enhanced SNat VObj VHomSet where 
>   type C a b = Preorder a b
>   ecomp = eComp1

I think that, with increasing support for dependent typing, enhanced categories could become 
a practical and sound way of writing code! 

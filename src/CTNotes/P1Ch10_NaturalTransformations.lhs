|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch10_NaturalTransformations

TODO work in progress

CTFP Part 1 Chapter 10. Natural Transformations
===============================================
Natural Transformations (NTs for short) are building blocks to a lot of category theory and are ubiquitous in Haskell.
If good programming is about composability then we got to study NTs. NTs can be composed in more than one way.

These notes assume familiarity with 
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) 
[Ch 10](https://bartoszmilewski.com/2015/04/07/natural-transformations/).

> {-# LANGUAGE Rank2Types #-}
> {-# LANGUAGE TypeOperators #-}
>
> module CTNotes.P1Ch10_NaturalTransformations where
>
> import qualified Control.Category as Cat
> import CTNotes.P1Ch07_Functors_Composition ((:.), isoFCA1, isoFCA2)
> import qualified Data.Functor.Compose as FComp
> import Data.Functor.Identity (Identity(..))
> import Data.Functor.Const (Const(..))
> import Control.Monad (join)

Typically, Natural Transformations are defined using `~>` type operator.
This is the case for Scalaz and Purescript. To keep with my convention of prefixing
type operators with `:` I will define it as `:~>`.  Other than using type operator (`TypeOperators` pragma is required), 
this definition matches the book.

> infixr 0 :~>
> type f :~> g = forall x. f x -> g x

This requires language to support universally quantified types. Both `Rank2Types` and `RankNTypes` pragmas
suffice. This means that functions from type `f x` to type `g x` that are polymorphic in type parameter x.  
With type operators, for example, we could write

> safeHead :: [] :~> Maybe  
> safeHead [] = Nothing
> safeHead (x:xs) = Just x

instead of 
```
safeHead :: [a] :~> Maybe a
```
The above definition of NT is oriented towards `Data.Functor` functors. However, it seems to be general enough.
For example, the following definition for bifunctors (which are functors too) is not interesting:

> type f :~~> g = forall x y. f x y -> g x y

It amounts to establishing NT for each type variable separately. 
For example, `type f :~~> g` is equivalent to `forall x . f x :~> g x` as shown here:

> rep :: f :~~> g -> forall x . f x :~> g x
> rep = id


Recap. Vertical Composition
---------------------------
Vertical composition of NT-ies reduces to function composition `(.)`. 
That works because composition of two functions that happen to be polymorphic must also be polymorphic.

> verticalComp :: g :~> h -> f :~> g -> f :~> h
> verticalComp gh fg = gh . fg


Recap. Naturality condition
---------------------------
We are interested in functions `f a -> g b`.
Natural transformation allows as to move between functors `f` and `g`, function `a -> b` moves us between types.
Combining these, allows to change both functor and type and move `f a -> g b`.  
However, we can accomplish that in two different ways:

> naturality1 :: Functor g => f :~> g -> (a -> b) -> f a -> g b
> naturality1 alpha f = fmap f . alpha
>
> naturality2 :: Functor f => f :~> g -> (a -> b) -> f a -> g b
> naturality2 alpha f = alpha . fmap f

(Read this as: if I have an NT `f :~> g` and a function `(a -> b)`, I can change both: `f a -> g b`.)   
Category Theoretical definition of Natural Transformation says that both approaches need to commute (yield the same result).
What is amazing is that in programming you get this for FREE!  If both `f` and `g` are functors, 
static code analysis can safely replace one code with the other if it feels like it will make thing better or faster. 
Interchange laws like this one are also very useful in equational reasoning on code.

The actual formula in Category Theory repeated from the book is:
```
   fmap_G f . alpha_a == alpha_b . fmap_F f
```
but because alpha is polymorphic we can drop underscored types `a` and `b`. Compiler can reconstruct/infer which functor 
type to use for fmap and this can be dropped as well.


Functor Category
----------------
Functors form a category (Functors are objects and NTs are morphisms). 
We can express this using `Category` typeclass defined in Control.Category module included in the base package.

> newtype NTVert f g = NTVert { ntVert :: f :~> g }
>
> instance Cat.Category (NTVert) where
>    id = NTVert id
>    NTVert f . NTVert g = NTVert (f `verticalComp` g)

(`id` in `NTVert id` is the polymorphic identity `id :: a -> a` function.)  
Proving the category laws is trivial since the vertical composition reduces to function composition.


Horizontal Composition
----------------------
Horizontal composition of NT-ies is an NT between composed functors, repeating the book:  
 α :: F -> F'  
 β :: G -> G'  
 β ∘ α :: G ∘ F -> G'∘ F'  

In general we would have something like 
    G'α_a ∘ β_Fa  == β_F'a ∘ G α_a

β ∘ α is sometimes called Godement product and the above isomorphism Godement interchange law.  
I like to think that this composition is called horizontal because (vertical) NTs are pushed 
forward by (horizontal) functors.

Parametricity/polymorphism arguments make horizontal composition simpler in Haskell:

> horizontalComp1 :: Functor g =>
>                     g :~> g' -> f :~> f' -> g :. f :~> g' :. f'
> horizontalComp1 beta alpha =
>    (\(FComp.Compose x) -> FComp.Compose $ beta . fmap alpha $ x)
>
> horizontalComp2 :: Functor g' =>
>                    g :~> g' -> f :~> f' -> g :. f :~> g' :. f'
> horizontalComp2 beta alpha =
>    (\(FComp.Compose x) -> FComp.Compose $ fmap alpha . beta $ x)

Again, we get `horizontalComp1 '==' horizontalComp2` and static code analysis can swap one code for the other. 
We have another tool for equational reasoning too.  
This is really nice!

Note 1: In the above formulas (from the CT point of view) (.) represents Hask morphism so it should be viewed as 
function composition, not vertical composition of NTs.   
Note 2: all of these should be Functors but for the implementation we just need one.  
TODO: do we need all of them to be functors for the interchange law to hold in Haskell?  
Note 3: a much simpler implementation of `horizontalComp1` given by `fmap (beta . fmap alpha)` does not compile.  
GHC infers the same types on both sides:
```  
 Expected type: (:.) b1 a1 x -> (:.) b2 a2 x  
    Actual type: FComp.Compose b2 a2 (b1 (a1 x0))
                 -> FComp.Compose b2 a2 (b2 (a2 x0))
```

Interchange Law
---------------
We have two types of compositions and they enjoy this nice distribution formula:  
     (β' ⋅ α') ∘ (β ⋅ α) = (β' ∘ β) ⋅ (α' ∘ α)

In this formula (.) is vertical and (∘) is horizontal composition 
(not that it would look much different if the notation was swapped).   
Another perfect tool to have for static analysis swaps or equational reasoning.

I will quote Milewski quoting Mac Lane:
"I will quote Saunders Mac Lane here: The reader may enjoy writing down the evident diagrams needed to prove this fact."

Here is LHS of this formula in Haskell, thank You typechecker!

> lhs :: (Functor f1, Functor f2, Functor f3, Functor g1, Functor g2, Functor g3)  => 
>         f2 :~> f3 -> f1 :~> f2 -> g2 :~> g3 -> g1 :~> g2 -> f1 :. g1 :~> f3 :. g3
> lhs beta2 alpha2 beta1 alpha1 = 
>        (beta2 `verticalComp` alpha2) `horizontalComp1` (beta1 `verticalComp` alpha1)

The hard part was getting the types right in the declaration for `lhs`. What would happen if we keep the same type signature and
variable names and just use the above interchange law to swap the implementation of `lhs`?
Here is the swapped version under new name `rhs`:

> rhs :: (Functor f1, Functor f2, Functor f3, Functor g1, Functor g2, Functor g3)  => 
>          f2 :~> f3 -> f1 :~> f2 -> g2 :~> g3 -> g1 :~> g2 -> f1 :. g1 :~> f3 :. g3
> rhs beta2 alpha2 beta1 alpha1 = 
>     (beta2 `horizontalComp1` beta1) `verticalComp` (alpha2 `horizontalComp2` alpha1)

(I also used one horizontalComp1 and one horizontalComp2 just because I am allowed!)
It typechecks! That is good news, GHC compiler does not have a problem with the interchange law and accepted my blind swap.

Equational reasoning that shows lhs == rhs is somewhat complex, starting at `rhs`:
```
  rhs                                                                             ==
  (beta2 `horizontalComp1` beta1) `verticalComp` (alpha2 `horizontalComp1` alpha1)==  
                     -- definition of verticalComp
  (beta2 `horizontalComp1` beta1) . (alpha2 `horizontalComp2` alpha1)             ==  
                     -- definition of horizontalComp
  (\ Compose x -> Compose $ beta2 . fmap beta1 $ x) . 
                               (\ Compose x -> Compose $ fmap alpha1 . alpha2 $ x)== 
                     -- Compose is a simple constructor with trivial patter match
  (\ Compose x -> Compose $ beta2 . fmap beta1 $ fmap alpha1 . alpha2 $ x)        ==  
                     -- fmap commutes with (.)
  (\ Compose x -> Compose $ beta2 . fmap (beta1 . alpha1) . alpha2 $ x)           ==    
                     -- Godement interchange applied to (beta1 . alpha1) and alpha2
                     -- see naturality1 and naturality2 above
  \ Compose x -> Compose $ (beta2 . alpha2) . fmap (beta1 . alpha1) $ x           ==  
                     -- definition of horizontalComp
  (beta2 . alpha2) `horizontalComp1` (beta1 . alpha1)                             ==  
                     -- definition of verticalComp
  (beta2 `verticalComp` alpha2) `horizontalComp1` (beta1 `verticalComp` alpha1)   ==  
  lhs 
```


Horizontal composition as morphisms between categories 
------------------------------------------------------
Horizontally composed NTs work on composed functors β ∘ α :: G ∘ F -> G'∘ F'.
In general case these do not need to be endofunctors so if F :: C -> D and G :: D -> E, G ∘ F:: C -> E
(rinse and repeat for primes) then we can neatly think of NTs mapping the same categories as functors do
α:: C -> D and β:: D -> E, β ∘ α:: C -> E.   
In Haskell that all flattens out and we have
F :: Hask -> Hask and G :: Hask -> v, G ∘ F:: Hask -> Hask and the neatly converted 
α:: Hask -> Hask and β:: Hask -> Hask, β ∘ α:: Hask -> Hask is not interesting.  
For programming, the devil is in the detail so the precise type signature (above) is what we want.

I can at least verify category laws.   
Following the book the identity morphism is natural tranformation 
of the type `Identity :~> Identity` 
(Identity defined in base package Data.Functor.Identity module and `id` is the identity function.) 

> ntId:: Identity :~> Identity
> ntId = id

That makes right and left identity laws trivial. 
  
Associativity: (γ ∘ β) ∘ α == γ ∘ (β ∘ α), assume α, β as above and γ :: H -> H`.  
Because of how we typed the 
[functor composition](https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch07_Functors_Composition)
LHS and RHS have different (but isomorphic) types:  
 (γ ∘ β) ∘ α:: (H ∘ G) ∘ F -> (H'∘ G') ∘ F'  
 γ ∘ (β ∘ α):: H ∘ (G ∘ F) -> H'∘ (G'∘ F')  

This shows one side of that type isomorphism (the other side is equally easy): 

> assoIso1:: (Functor f, Functor f', Functor g, Functor g',Functor h, Functor h') =>
>            (h :. g) :. f :~> (h' :. g') :. f' -> h :. (g :. f) :~> h' :. (g' :. f')
> assoIso1 nt = isoFCA1 . nt . isoFCA2


(TODO needs some polish.) Equational reasoning about the associativity 
(lying a little bit by ignoring `Compose` data constructor):
```
  gamma `horizontalComp1` (beta `horizontalComp1` alpha) ==
  gamma . fmap (beta . fmap alpha)                       ==
     -- fmap commutes with (.)
  gamma . fmap beta . (fmap . fmap) alpha                ==
     -- composition of 2 functors is a functor
  gamma . fmap beta . fmap alpha                         ==
     -- function composition is associative              ==
  (gamma . fmap beta ) . fmap alpha                      ==   
  (gamma `horizontalComp1` beta) `horizontalComp1` alpha
```

Implementing KCategory class with kind constraints from 
[N_P1Ch07_Functors_Composition](https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P1Ch07_Functors_Composition)
is not that interesting and I will skip it.


Code examples
-------------
Natural Transformations are ubiquitous in Haskell as is the use of polymorphic functions. Even polymorphic functions 
that do not look like `f a -> g a` end up being NTies.  Book has this intersting example:

> lengthIsNt :: [] :~> Const Int 
> lengthIsNt = Const . length

NTs involving `Reader r` have very special importance (Yoneda) and deserve separate set of notes.
Other examples: 

(to avoid package dependencies I am redefining this monad transformer here):

> newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }
> runMaybeTisNT :: MaybeT m :~> m :. Maybe
> runMaybeTisNT = FComp.Compose . runMaybeT
> maybeTisNT :: m :. Maybe :~> MaybeT m 
> maybeTisNT = MaybeT . FComp.getCompose

These examples are just quoted to avoid package dependencies:
 
```
liftIOIsNT ::  MonadIO m =>  IO :~> m
liftIOIsNT = liftIO

liftIsNT :: (MonadTrans t, Monad m) => m :~> t m
liftIsNT = lift

atomicallyIsNt :: STM :~> IO
atomicallyIsNt = atomically
```
I sometimes see natural transformations explicitly called out in the code (typically by using `~>`) to emphasize 
type transformation.  For example, DSL implementations that map abstract syntax instructions to interpreter, 
or transformation of effects.

__Composition__. Vertical composition of NTies reduces to `(.)` and is obviously used a lot.
Horizontal composition hides in code patterns like `fmap f . g` used with composed types.  
But here is some fun with it:

> safeHead2 :: [] :. [] :~> Maybe :. Maybe
> safeHead2 = safeHead `horizontalComp1` safeHead

and notice that (join is a natural transformation [Part 3, Ch.7](https://bartoszmilewski.com/2016/12/27/monads-categorically/)):

> reduceDoubleMaybe :: Maybe :. Maybe :~> Maybe
> reduceDoubleMaybe = join . FComp.getCompose

Is that not nice! We just composed vertically and horizontally: `join . (safeHead ∘ safeHead)`.  


TODO maybe isos should use ~= and for actual equals use == ?
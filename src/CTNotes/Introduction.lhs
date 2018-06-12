_I posted a pandoc copy of this document on my [blog](http://rpeszek.blogspot.com/2018/02/why-read-ctfp-why-study-category-theory.html). 
If you would like to leave a comment please do so on that page._

Why read CTFP?  Why study category theory?
==========================================

> module CTNotes.Introduction where

I finished my second (I am sure not the last) reading of Milewski's book.
This note is about what motivated me to read CTFP and why I think we need this book.  
At work, my group is in the midst of a very serious refactoring and a technology shift.  That change
follows months of technical discussions.  My experiences at work have motivated this note as well. 
I cannot help but ask myself: how different would all of this have been if my coworkers have read CTFP? 
And, since we use Java at work, I will use the Java ecosystem as a source of examples.
 
We live in the google and stackoverflow times.  Only very few read programming books. Deadlines are deadlines, there is just 
no time for reading and linear learning. Yet, there are limits to google search learning. Books are needed!

__Why this particular book?__  
There are other books about category theory written for programmers. 
In my opinion, CTFP is unique in 2 ways: 

* it covers lots of ground, more than any of the other books
* it manages to stay very intuitive and relevant to programming  

Personally, I really appreciate the second bullet. 

__Why learn category theory?__  
Category theory is not intuitive (not to me). It is different from ground-up. 
It redefines everything starting with basic concepts like sum, product, exponent. 
Being different is good. Think about a toolbox with only one type of screwdriver in it, I want more tools in my toolbox.

Category theory uncovers common structures in computations. These structures allows 
us to understand computations in ways not possible otherwise. Category theory allows to identify similarities between
seemingly disparate concepts. It tells us that the code has properties (obeys laws) and what these properties (laws) are. 
But it gets even more fundamental than this.
 

Trinity of Computer Science, Practical Trinitarianism
-----------------------------------------------------
The term was coined by Robert Harper ([post](https://existentialtype.wordpress.com/2011/03/27/the-holy-trinity/)) 
and is relatively new (2011) but the concept is old 
(Curry-Howard correspondence between programming and logic can be placed between 1934-1969, 
Curry-Howard-Lambek correspondence that includes category theory is early 1970s).
At some point in the future (when we discover and understand more) trinitarianism will become 
[quadrinitarianism](http://comonad.com/reader/2018/computational-quadrinitarianism-curious-correspondences-go-cubical/)
but that is another story.  

To me, trinitarianism means that I have 3 tools when designing and developing programs:

* Proof Theory
* Type Theory
* Category Theory

They may all be equivalent, but as toolsets each offers a unique set of benefits.
They are the three manifestations of the notion of computation.

Philip Wadler distinguishes languages that were created (like Java) from languages that were
discovered (like various Lambda Calculi).  Other than the scope, this is equivalent to Harper's concept of the divine.  
Software engineers love arguing which code is better (can you get better than a divine?).
Correspondence to logic is really the best comparator is in such arguments.

We can question many things, say, the use of Hibernate (a library in the Java ecosystem) or even something like 
the Java language design itself.
Similar question do not even make sense with respect to the Lambek correspondence.
These 3 manifestations of code simply are. Questioning that correspondence is like questioning 
Pythagorean theorem. 
What we can and often do, however, is to just ignore it!  

Software engineering is founded on a belief that logical problems can be solved without 
any training in logic. Despite being self-contradictory, this approach works surprisingly well for many
software products. The limitation of this approach is that it does not scale well with logical complexity. 
Majority of software engineers do not acknowledge this limitation. 
We all have a tendency to de-emphasize importance of things we do not understand. 
Learning the trinity (including category theory) is admitting to the existence of that limitation and 
admitting to the importance of logic.

Divine computation sounds like something very academic and out of reach of a mortal programmer. It is not! 
Remember, we live in the _stackoverflow_ times and we copy-paste programs. 
Copy-paste of a divine is still divine.
The only problem is how to recognize that divine aspect?  
Hmm, only if there were books about it, or if there was some catalog of divine computations 
(like something called a category theory)...


Beginner Trinitarianist
-----------------------      
First steps are as simple as a change in the attitude. 
When designing my app I look for soundness and strong theoretical properties. I want to use building blocks 
that are logically sound. I want to write code that is type-safe. 

Let me start by discussing what the trinity is not.  
Take type safety as an example and think about Java `Object` class with its 11 methods.
These methods can be invoked on any object, `"boo".equals(5)` compiles just fine, comparison between 
a String and an Integer always returns `false`, 
and there is almost 100% chance that comparing a String to an Integer is an escaped bug! 

Take strong theoretical properties and soundness as the next example. Category theory offers a set of 
programming tools such as monoids, monads, natural transformations. 
Any application has them, you really have no choice about it, the only choice that you
have is whether to ignore these computational structures or not. 
All of these come with strong theoretical properties or laws.  
Laws are what is important.  Consider this code that uses Java standard library 
(I am not indicating the Java version, I am quite sure this will never get fixed)
```Groovy
groovy>  //using Groovy console as a replacement for REPL to see what Java will do
groovy>  import java.sql.Timestamp
groovy>  import java.util.Date
groovy>   
groovy>  Date d = new Date()
groovy>  Timestamp t = new Timestamp(d.getTime())
groovy>  [t.equals(d), d.equals(t)]

Result: [false, true]
```
nothing good can possibly come out of equals not being symmetric!   
Exercise for Java coders: play with Java comparators using Dates and Timestamps, 
is `<` antisymmetric for objects in Java standard library?  
Better Exercise: try to fix it (fix Java source for Date and Timestamp so equals is symmetric). 
It is not that easy!  
  
Here is a fun example violating requirements defined by 
[java.util.Set.equals](https://docs.oracle.com/javase/8/docs/api/java/util/Set.html#equals-java.lang.Object-), 
using Groovy (tested with Groovy v.2.4.10):  
```Groovy
groovy>  def x= [] as Set
groovy>  def y= "".split(",") as Set
groovy>  
groovy>  [x == y, x, y]

Result:  [false, [], []]  
```
Bugs like this impact thousands (Groovy) to millions (Java) of software engineers, 
the economic cost must be significant.  
_Side-note: in the last example `x` and `y` are two different implementations of Java Set._
_I am exploiting a common pattern, binary relations and object inheritance do not mix well._

There is more than one point here: 

* Laws are important and so is proving/certifying them
* Wadler was right and one way to spot a trinitarianist is by his/her selection of the computing language environment.

__Trust__.  I had tried to convey this idea with a limited success. As an engineer I do not need
to understand monoids, monads, functors, etc, to use them!  I only need to trust that they are important and learn their plumbing. 
I still will rip the benefits of code that has better correspondence to logic, it will be less buggy and easier to maintain.
This speaks to the very idea of good engineering. Engineering is about applying science and mathematics to solve practical problems. 
Great engineers do not need the depth of mathematical knowledge. What they need is a level of trust in The Queen.  

CTFP is a great companion here. It covers lots of ground while being intuitive and interesting to read. It delivers a list
of useful concepts and helps building that _trust_.  CTFP replaces fear of formalism with curiosity. Curiosity is what writes 
interesting programs.  
My goal, in my first reading of CTFP, was to just get the concepts down and to start applying them in my code (often blindly).
 
 
Intermediate Trinitarianist
---------------------------  
Next steps are as simple as defining the application types and then thinking what kind of theorems 
I can prove about these types.  Consider this very simple (and incomplete) example

> data HTML = NeedsWork | NeedsImagination
>
> data FancyTree a = SomethingInteresting
> 
> -- without typeclasses
> fancyTreeToHTML :: (a -> HTML) -> FancyTree a -> HTML
> fancyTreeToHTML = undefined
>
> -- with typeclasses
> class ToHTML a where
>   toHTML :: a -> HTML
>
> instance ToHTML a => ToHTML (FancyTree a) where 
>   toHTML = undefined

As an engineer I can think that I am implementing HTML rendering using polymorphism and leveraging other code.
As a trinitarianist I see theorems and proofs (well, not proofs because I was lazy and have used `undefined`).  
`instance` definition is a theorem and so is the type signature of `fancyTreeToHTML`.
For a trinitarianist, `->` and `=>` are the modus ponens!  
Trinitarianist views code like this as proving ToHTML theorems about the application types.  
The above code may differ or go beyond the straightforward mapping in the Curry-Howard correspondence, 
but from a pragmatic standpoint, the mapping to logical derivation remains clear and effective.  
The slogan is: types are theorems and programs are proofs, and this code reflects the slogan well.

Continuing with the equals saga: not everything can be compared with everything, being able to compare 
elements of type `a` is a theorem `Eq a`. For simple types (called _ADT_) that theorem is a simple boilerplate
but not so for more complex types.  
So, for example, removing duplicates form `[a]` is a theorem that assumes evidence of `Eq a`

> myNup :: Eq a => [a] -> [a]
> myNup = undefined 

That sounds like "this's just semantics".  Right on!  It is just semantics, but only for code that is close to logic.
Pick some Java program at random and try to think about it as theorems and proofs.
That will not work so well, will it?

Since logic and programming are one and the same, it is nice when the programming language supports
logical concepts such as universal or existential quantification (the forall and exists quantifiers in logic). 
These are the System F type constructions that also have important categorical representations 
(for example, see [(co)limits, N_P2Ch02a_LimitsColimitsExtras](N_P2Ch02a_LimitsColimitsExtras)).  
Trinity complements each other.
 
Remember, the end goal is to have more correct or even certifiable programs.  
More advanced uses of types allow compiler to verify all kinds of things. 
Here are some examples I have played with in this project:
 * [N_P2Ch02b_Continuity](N_P2Ch02b_Continuity) compiler checks type cardinality [N_P2Ch02b_Continuity](N_P2Ch02b_Continuity), 
 * [N_P3Ch15b_CatsAsMonads](N_P3Ch15b_CatsAsMonads) compiler helps me verify that 2-cell `mu` in the bicategory of spans is 
 the same as the composition in the underlying category. 
  
There are limits to what compiler can do and pencil and paper proofs are still needed. 
However, this situation is changing, see this blog about
[proofs of laws](https://blog.jle.im/entry/verified-instances-in-haskell.html),  
or this example in my IdrisTddNotes project
[Functor laws, Idris vs Haskell](https://github.com/rpeszek/IdrisTddNotes/wiki/Play_FunctorLaws). 
 

A lot of programming is about verifying that programs are equivalent, replaceable.
Finding if given 2 lambda expressions are equivalent is undecidable. 
Static analysis tools (AI or not) are unlikely to automate this.
One big ticket item here is the task of _refactoring_ where, typically, things 
should work the same before and after (think performance refactoring). 
A trinitarianist will use tools like equational reasoning, or maybe some form of structural induction
to certify correctness of refactoring.
Category theory augments this with a nice set of ready refactoring tools (like the Yonada transformation).

Or, instead of me refactoring, the compiler could rewrite the code and optimize it.
This idea extends nicely to fusion/code rewrite optimizations available in Haskell's Core (Haskell
compiles to an intermediate language which is a lambda calculus and is programmable). 
Respect for logic == high performance!
Tools like Yonada transformation are especially important in languages where fusion is not an option.

Any trinitarianist will be interested in the language design. Designing domain specific languages 
allows programmers to define their own semantic rules. These are the rules for formal reasoning on the code.
Category theory supplies DSL creating tools such as free monad and cofree comonad. 
The power of trinity is in combining all of the 3! 

More advanced use of categories means that I

 * Prove laws about my computations. 
 * Use a toolbox of certified refactoring solutions.  
 * Have certified tools for creating DSLs.  
 * Use category theory to come up with how to do stuff, for example program with diagrams! 
 See [N_P1Ch08b_BiFunctorComposition](N_P1Ch08b_BiFunctorComposition), [N_P3Ch02a_CurryAdj](N_P3Ch02a_CurryAdj), 
 or [N_P3Ch02c_AdjProps](N_P3Ch02c_AdjProps)
 * Understand why some code looks so similar to other [N_P3Ch11a_KanExt](N_P3Ch11a_KanExt)
 * Better understand computational structure, for example iso-recursion [N_P3Ch08a_Falg](N_P3Ch08a_Falg) 
 * Use categories in defining business requirements (that is something I would like to research more.)

and so on..

Current industry and social bias against formalism and mathematics may prevent people from writing code that looks 
like proofs. At the same time, I am very convinced that anyone capable of learning how to program can learn 
how to write proofs. The hardest part about either task is being able to survive the confinement of 
removed ambiguity (no hand-waving). Unfortunately, can does not mean will. 
Category theory offers a partial work-around here. It allows engineers to implement 
code using logically solid building blocks while someone else has certified the correctness. 
Again it is about that _trust in the queen_ idea I wrote about earlier.

CTFP is a great companion to an intermediate trinitarianist. I can re-read parts of it, 
it builds base knowledge, prepares me to do more research. 
I do not want to admit to how many times I re-read some of the chapters.


Conclusions
-----------
There appear to be 2 very different parts to writing software:  programming and software engineering.  
They are different because programming has a direct correspondence to logic, software engineering does not.

Programming is about logic, proofs, types, categories.  
Programming is about certifiable software and provable correctness.  
Programming is about audacity of using logic when solving logical problems.   
Software engineering is pragmatic, suspicious of formalism, and has deadlines.  
Software engineering is about correctness by a lot and lot of testing effort (and, often, ignoring provable incorrectness).  

Programming is a very small share of the overall software development (looking at language usage statistics
suggest about 1%). My personal interest and bias is clearly on the programming side but I do think of
myself as an engineer too. I think current balance point is just wrong, there needs to be more that 1% market share
of programming in software!
  
Besides, that 1% just proves my point. Writing code is like skiing, driving a car, or anything else.
Just look at what everyone is doing, do exactly the opposite and you will be just fine.

Many software engineers feel personally offended by some of this. 
If anywhere, the blame should be placed on education. I wish I had something like CTFP when I started learning
how to program. I was a 3rd year student immersed in pure mathematics. The instruction made
no use of anything I knew already. Not even mid school/high school algebra. Think about 
`(a ^ b) ^ c = a ^ (c * a)` or `a ^ (b + c) = a^b * a^c` we know as currying and pattern match, nope.
The opportunity to leverage concepts I knew well was lost.
I think CS education has failed me and has failed most of us. 
Hopefully this situation will change 
([CMU new curriculum](https://www.cmu.edu/news/archive/2011/May/may2_introcompsci.shtml)).
For us old-timers, there are some good books that connect the dots, books like CTFP. 

Category theory is one of the big three. It offers logical solutions to programming problems. 
It offers understanding of the code structure. 
CTFP is currently the best book to learn it if you are a coder and not a working mathematician. 
It is not a very hard reading. What are you waiting for? 

Would we be making different technology decisions if we read CTFP?  Yes. 

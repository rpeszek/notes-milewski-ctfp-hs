
__Early Draft__  
__WORK IN PROGRESS__  

Why read CTFP?  Why study category theory?
==========================================

> module CTNotes.Introduction where

I finished my second (I am sure not last) reading of Milewski's book.       
This note is about what motivated me to read CTFP and why I think we need this book.  
At work, my group is working on a very serious refactoring and a technology shift.  That change
follows months of technical discussions.  My experiences at work have motivated this note as well. 
I cannot help but ask myself: how different would all of this have been if my coworkers have read CTFP? 
 
We live in the __stackoverflow__ times.  Only very few read programming books. Deadlines are deadlines, there is just 
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
 

Trinity of Computer Science, Practical trinitarianism
-----------------------------------------------------
The term was coined by Robert Harper ([post](https://existentialtype.wordpress.com/2011/03/27/the-holy-trinity/)) 
and is relatively new (2011) but the concept is old (Curry-Howard-Lambek correspondence, 1970s).  
At some point in the future (when we discover more) trinitarianism will become 
[quadrinitarianism](http://comonad.com/reader/2018/computational-quadrinitarianism-curious-correspondences-go-cubical/)
but that is another story.  

To me, trinitarianism means that I have 3 tools when designing and developing programs:
* Proof Theory
* Type Theory
* Category Theory

They may all be equivalent, but as tool sets each offers a unique set of benefits.
They are the three manifestations of the notion of computation.

Philip Wadler distinguishes languages that were created (like one I use at work called Java) from languages that were
discovered (like various Lambda Calculi).  Other then the scope, this is equivalent to Harper's concept of the divine.  
Software engineers love arguing which code is better (can you get better than a divine?).
These arguments involve a lot of hand-waving.
Correspondence to logic is really the best comparator is in such arguments.

Divine computation sounds like something out of reach of a moral programmer. It is not! 
Remember, we live in the _stackoverflow_ times and we copy-paste programs. 
Copy-paste of a divine is still divine.
The only problem is how to recognize that divine aspect?  
Hmm, only if there were books about it, or if there was some catalog of divine computations 
(like something called a category theory)...

We can question many things, say, the use of Hibernate (a library in the Java ecosystem) or even something like 
the Java language design itself.
Similar question do not even make sense with respect to the Lambek correspondence.
These 3 manifestations of code simply are. Questioning that correspondence is like questioning 
Pythagorean Theorem. 
What we can and often do, however, is just ignore it!  
This is what software engineers have been doing for years. 

Software engineering was founded on a belief that complex logical problems can be solved without 
any training in logic. Despite being self-contradictory, this approach worked surprisingly well for many
software products. The limitation of this approach is that it does not scale well with logical complexity. 
Learning category theory is admitting to the existence of that limitation and to the importance of logic.


__Beginner Trinitarianist__      
First steps are as simple as a change in the attitude. 
When designing my app I look for soundness and strong theoretical properties. I want to use building blocks 
that logically sound. I want to write code that is type-safe. 

Take just type safety as an example and think about Java Object class with its lucky 13? methods.
These methods can be invoked on any object, `"boo".equals(5)` compiles just fine, comparison between 
String and Integer always returns `false`, 
and there is a 99.9% chance that comparing String to Integer is an escaped bug! 

In reality, any app has monoids, monads, natural transformations, etc, ignoring these is dangerous.
Monoids, monads, and natural transformations are categorical concepts that come with laws.
Laws are important.  Consider this code that uses Java standard library (notice, I am not indicating the Java version, 
I am quite sure this will never get fixed)
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
(Exercise for Java coders: play with Java comparators using Dates and Timestamps, 
is `<` antisymmetric for objects in Java standard library?
Better Exercise: try to fix it (fix Java source for Date and Timestamp). Not so easy, is it!)  
  
Software engineers do not lose any slip over it. We all have a tendency to de-emphasize importance of things 
we do not understand. Unfortunately, logic is not very forgiving. 
Analogy: not understanding electricity does not make us immune from getting electrocuted.  

Here is a fun example violating requirements defined by 
[java.util.Set.equals](https://docs.oracle.com/javase/8/docs/api/java/util/Set.html#equals-java.lang.Object-), 
this time more Groovy (tested with Groovy v.2.4.10):  
```Groovy
groovy>  def x= [] as Set
groovy>  def y= "".split(",") as Set
groovy>  
groovy>  [x == y, x, y]

Result:  [false, [], []]  // ~~~buzz, buzz, bzzz, hair standing on end
```
Implementing equals in Java is far from trivial. You often need to consider a whole universe of subtypes to do it well. 
This one at least appears to be symmetric, `y == x` prints `false`.
There is more than one point here: the laws are important and Wadler is right, 
some language environments are just not logic friendly.


__Trust__.  I had tried to convey this idea at work but I have failed. As an engineer I do not need
to understand monoids, monads, functors, etc, to use them!  I only need to trust that they are important and learn their plumbing. 
I still will rip the benefits of code that has better correspondence to logic, it will be less buggy and easier to maintain.
This speaks to the very idea of good engineering. Engineering is about applying science and mathematics to solve practical problems. 
Great engineers do not need the depth of mathematical knowledge. What they need is the trust in The Queen.  

CTFP is a great companion here. It covers lots of ground while being intuitive and interesting to read. It delivers a list
of useful concepts and helps building that _trust_.  CTFP replaces fear of formalism with curiosity. Curiosity is what writes 
interesting programs.
My goal in my first reading of CTFP was to just get the concepts down and to start applying them to my code (often blindly).
 
 
__Intermediate Trinitarianist__  
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

As an engineer I can think that I am implementing HTML rendering leveraging other code.
As a trinitarianist I see theorems and proofs (well, not proofs because I was lazy and have used `undefined`).  
`instance` definition is a theorem and so is the type signature of `fancyTreeToHTML`.
For a trinitarianist, `->` and `=>` are the modus ponens!  
Trinitarianist views code like this as proving ToHTML theorems about the application types.

That sounds like "this's just semantics".  Right on!  It is just semantics, but only for code that is close to logic.
Pick some Java program at random and try to think about it as theorems and proofs.  That will not work so well, will it?

A more advanced use of types allows me to use compiler to verify things for me. 
Here are some examples I have played with in this project:
 * [N_P2Ch02b_Continuity](N_P2Ch02b_Continuity) Compiler checks type cardinality [N_P2Ch02b_Continuity](N_P2Ch02b_Continuity), 
 * [N_P3Ch15b_CatsAsMonads](N_P3Ch15b_CatsAsMonads) compiler verifies that 2-cell `mu` in the bicategory of spans is 
 the same as the arrow composition. 
  
There are limits to what compiler can do (especially true in a language like Haskell) 
and pencil and paper proofs are still needed. Proofs are often like unit tests that take no time to execute
and are valid across all possible data scenarios.

A lot of programming is about verifying that things are equivalent, isomorphic in some way.
One big ticket item here is refactoring, typically the refactored parts of code should work the same before and after. 
_Equational reasoning_ is the go to technique here but category theory provides a nice set of ready tools 
for stuff like this (like the Yonada transformation). 

More advanced use of Categories means that I
 * Prove laws about my computations. 
 * Use a toolbox of refactoring solutions.  
 * Use category theory to come up with how to do stuff, for example program with diagrams! 
 See [N_P1Ch08b_BiFunctorComposition](N_P1Ch08b_BiFunctorComposition), [N_P3Ch02a_CurryAdj](N_P3Ch02a_CurryAdj), 
 or [N_P3Ch02c_AdjProps](N_P3Ch02c_AdjProps)
 * Understand why some code looks so similar to other [N_P3Ch11a_KanExt](N_P3Ch11a_KanExt)
 * Better understand computational structure, for example iso-recursion [N_P3Ch08a_Falg](N_P3Ch08a_Falg) 
 * Use categories in defining business requirements (that is something I would like to research more.)

and so on..

Current industry and social bias against formalism and mathematics may prevent people from writing code that looks 
anything like proofs. At the same time, I am very convinced that anyone capable of learning how to program can learn 
how to write proofs. The hardest part about either task is being able to survive confinement of 
removed ambiguity (no hand-waving). Unfortunately, can does not mean will. 
Category theory offers a partial work-around here. It allows engineers to implement 
code using logically solid building blocks while someone else has written the proofs. 
Again it is about that _trust in the queen_ idea I wrote about earlier.

CTFP is a great companion to an intermediate trinitarianist. I can re-read parts of it, 
it builds base knowledge, prepares me to do more research. 
I do not want to admit to how many times I re-read some of the chapters.


Conclusions
-----------
There appear to be 2 very different parts to writing software:  programming and engineering.  

Programming is about logic, proofs, types, categories.  
Programming is about provable correctness.  
Engineering is pragmatic, suspicious of formalism, and has deadlines.  
Engineering is about correctness by a lot and lot of testing effort (and, often, ignoring provable incorrectness).  

Programming is a very small share of the overall software development (looking at language usage statistics
suggest about 1%). My personal interest and bias is clearly on the programming side but I do think of
myself as an engineer too.  I think current balance point is just wrong, there needs to be more that 1% market share
of programming in software!
  
Besides, that 1% just proves my point. Writing code is like skiing, driving a car, or anything else.
Just look at what everyone else is doing, do exactly the opposite and you will be just fine.

Category theory is one of the big three. If offers bullet proof... No! more than bullet proof, it offers logical 
solutions to programming problems. It offers understanding of the code structure. 
CTFP is currently the best book to learn it if you are a coder and not a working mathematician. 
It is not a very hard reading. What are you waiting for? 

Would we be making different technology decisions if we read CTFP?  Yes. 

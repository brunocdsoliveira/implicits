%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Rule.fmt
%%include Scala.fmt
%format new = "\bf{new}"

%format === = "\cong"

\section{Discussion}\label{sec:discussion}

In this section we discuss and justify several of the design decisions made
during the creation of \name. Mostly, these choices are motivated by the design
of Haskell type classes or Scala implicits.

\subsection{Predicative Instantiation}

System F is an impredicative calculus, allowing the instantiation of type
variables with arbitrary (polymorphic) types. In contrast \name is predicative:
instantiation of type variables only allows \emph{monotypes}. Our reasons for
departing from System F are threefold:

\begin{itemize}

\item {\bf Impredicative instantiation in resolution leads to additional
ambiguity.} As discussed in Section~\ref{sec:ourlang}, impredicative
instantiations of type variables during resolution can lead to ambiguity. The
restriction to predicative instantiation removes this ambiguity, and we see no
way that preserves impredicativity to achieve the same. 

\item {\bf Impredicativity is complex for implicit instantiation.} While System F (where all type instantiations are
explicit) is simple, matters become much more complicated when some implicit
instantiation is allowed. Indeed, the design of System F-like calculi with
implicit instantiation and/or some form of
type-inference~\cite{odersky1996putting,jones2007practical,le2003ml,leijen2008hmf,vytiniotis2008fph}
is much
more divided in terms of design
choices regarding (im)predicativity. Notably, Rouvoet~\shortcite{Rouvoet} has shown that
the ambiguous resolution from the implicit calculus~\cite{oliveira12implicit}, which is the impredicative
variant of our Figure~\ref{fig:resolution1}, is undecidable. His proof proceeds by showing
that the problem is equivalent to the System F type inhabitation problem, which is 
known to be undecidable~\cite{lambdacalculus}.

% TOM: I don't think we need to say any of this anymore since Rouvoet already
% shows that ambiguous resolution is undecidable.
%
% One key complication has to do
% with the most-general relation for implicit
% polymorphism. The most-general relation allows systems with implicit 
% polymorphism to decide whether a type is an instance of another type. 
% For example the type |Int -> Int| is an instance of the polymorphic 
% type |forall a . a -> a|. An algorithm for determining whether a type
% is more general than another must perform implicit instantiation. 
% Unfortunately, it is well-known that for \emph{impredicative
%   instantiation}, the most-general relation is undecidable~\cite{tiuryn1996subtyping}. 
% However, when only predicative instantiation is allowed, then 
% the most-general relation is decidable~\cite{odersky1996putting,dunfield,zhao18formalization}. 
% Resolution in \name is closely related to the most-general relation 
% and we believe that, under impredicative instantiation, resolution is
% indeed undecidable.\bruno{This may actually be a known result. See Rouvet?}

\item {\bf Predicative instantiation is not a big restriction in
    practice.} 
Due to the above complications brought by impredicativity, many practical 
languages with type-inference only allow predicative instantiation.
For example, the key algorithm for type-inference currently employed 
by the GHC Haskell compiler is predicative~\cite{jones2007practical,Vytiniotis}.
Worth noting is that the original Hindley-Milner (HM)
type system~\cite{hindley69principal,milner78theory}
is where the predicativity restriction on polymorphic type
systems with type-inference was first put into place. 
Since \name is intended as a target for languages with 
implicit polymorphism and type-inference, which have
predicativity restrictions, restricting the core language to allow only
predicative instantiation does not pose any problems.

\end{itemize}

\paragraph{Alternative Design Choices} One alternative design choice
worth mentioning for \name would be to allow impredicative
instantiation in explicit type applications, but still retain the predicativity
restriction during resolution. This design would be less restrictive
than the design of \name, and we believe that it is a reasonable
design. We decided against it for two reasons. Firstly,
as already mentioned,
\name is aimed to be a target for source languages with
type-inference. As these source languages have predicative restrictions anyway, 
there is little to be gained from having impredicative instantiation
in the core. Secondly, and more importantly, some of the meta-theory
would be more involved if impredicative instantiation on type
applications were allowed. In particular, Lemmas~\ref{lem:stable:resolution}, \ref{lem:stable:typing} and \ref{lem:stable:correct} would need 
to be generalized to allow any types to be used in the substitution, rather than just
monotypes. This could be problematic since the impredicative instantiations
of the type variables could bring back the ambiguity issues discussed
in Section~\ref{sec:ourlang}. We expect that additional restrictions
would be needed at type applications to prevent instantiations
with problematic polymorphic types that would lead to ambiguity.

Allowing full impredicativity (both in type applications and
resolution) seems more complicated. We expect that such a design
is possible, but necessarily more complicated if ambiguity and
undecidability are to be avoided. We expect that the work on
impredicative type-inference~\cite{le2003ml,leijen2008hmf,vytiniotis2008fph} is relevant, and perhaps some 
of the design choices employed in those works would be helpful 
in the design of a system with full impredicativity.  

\subsection{Committed Choice}\label{sec:committed}

\name commits to the first implicit who's head matches the query type. It has
inherited this committed choice approach from Haskell. 
Consider for instance the following Haskell program with two overlapping instances:

%format dots ="\ldots"

> class C a where
>   m :: a -> a
>
> instance Eq a   => C [a] where dots
> instance Ord a  => C [a] where dots
> 
> f :: StablePtr Int -> [StablePtr Int]
> f sp = m [sp] 

This code declares a type class |C a| and defines two
instances. The first instance requires |Eq a|, whereas the second
instance requires |Ord a|. The function |f| takes a stable pointer
(|StablePointer|)
and returns a list of stable pointers. Unlike many other types, |StablePointer| only supports 
equality, and not ordering. That is, there is an
instance |Eq (StablePointer a)| but not one for |Ord (StablePointer a)|. 

Should the above code type-check or not? In GHC
Haskell the answer is no.  Even though there is no ambiguity in this program---
resolution only succeeds with the first type class instance---
the program is nevertheless rejected. The reason is that Haskell's resolution only checks whether
the instance heads match. As there two equality specific
matching heads |C [a]|, the program is rejected.


Although this Haskell design choice is not very well documented in the research
literature, the reason for not allowing backtracking is folklore among Haskell
programmers and can be found in documentation and emails~\cite{}\bruno{Tom: Can
you put some references here? (blogs, emails, documentation is fine)}.  In
essence there are two arguments for not allowing backtracking during
resolution:

\begin{itemize}

\item {\bf Reasoning:} When reasoning about Haskell code that involves
type classes, programmers have to understand which type class instance is used.
This involves performing the resolution algorithm manually. The
fact that only instance heads are needed to determine whether an instance is
committed to, makes this much easier than performing a full backtracking
process.

\item {\bf Performance:} If backtracking is allowed, 
type-checking times programs could grow exponentially due to
backtracking. Thus, by disallowing backtracking, GHC eliminates a potential
source of significant performance degradation in type-checking.

\end{itemize}

\paragraph{No Backtracking in \name} Like in Haskell, our committed choice design
for \name also looks only at the heads of rule types, whereas a design with backtracking
would need to look at their contexts as well.
In other words we commit to a matching rule type, even if
its recursive goals do not resolve. For instance, when resolving $\tychar$
against the environment $\tenv = ?\tybool, ?(\tybool \To \tychar), ?(\tyint \To
\tychar)$, we commit to $?(\tyint \To \tychar)$ even though its recursive goal $\tyint$
cannot be resolved and thus the resolution of $\tychar$ also fails. A more permissive
approach would be to backtrack when a recursive resolution fails and try the next
alternative matching rule. That would allow $\tychar$ to resolve. 

In the design of \name, we have followed Haskell's pragmatic reasons for committed choice.
Considering that Haskell's 30 years of experience have shown that this works well
in practice, we believe that it is a reasonable choice.

% While backtracking is a perfectly established technique in proof search and
% logic programming, it is often shunned in type checking algorithms for the
% pragmatic reasons given above. Here we have opted for a design that looks at the heads
% of rules only, following a similar design choice taken in Haskell. 

\paragraph{Alternative Designs} 
While there are advantages to committed choice, backtracking also has its
appeal and several systems have adopted it~\cite{DBLP:journals/corr/WhiteBY15,coqclasses}.
In particular, backtracking accepts more queries, and would allow us to have a
sound and complete algorithm for \name (instead of just a sound one) with
respect to Figure~\ref{fig:resolutionf}.
% However there are still some hurdles to be overcome in order to design a coherent and stable
% algorithm with backtracking. 
Yet, the specification in Figure~\ref{fig:resolutionf} does not guarantee
stability. So additional restrictions would be needed to prevent unstable
resolution.  

% In our work we have opted for an algorithm that follows some of the practical
% considerations that were discussed before in the Haskell community. The nearly
% 30 years of experience with Haskell type classes indicate that such a choice
% works reasonably well in practice. Nonetheless allowing backtracting does have
% better properties in theory, and despite the practical disadvantages with
% respect to committed choice, we think it is still a reasonable and worthwhile
% design to explore in the context of programming languages.

Ocaml's modular implicits~\cite{DBLP:journals/corr/WhiteBY15} suggest another alternative.
When a query is resolved, it exhaustively searches the implicit context for all 
possible solutions. If more than one solution is found, then the program is
rejected due to ambiguity. In this way it is possible to have highly overlapping
rules in the context, that could result in some queries being ambiguous.
One advantage of this design is its flexibility, since contexts can be more
liberal and all queries that would be resolved in unambiguous contexts with backtracking
can, in principle, also be resolved with Ocaml's modular implicits.
However the modular implicits approach is not formalized yet, and the fact that contexts
have to be searched exhaustively raises practical questions regarding performance and
ease of reasoning that have dictated the committed choice approach taken by Haskell type classes.

Finally, in the context of theorem provers like Coq~\cite{coqclasses} where
proof irrelevance typically holds, backtracking seems to be the better choice.
If type classes are supplying proofs and it does matter which proof is found,
coherence is not relevant, and the objection about the difficulty of reasoning is
also not relevant. 
Moreover, in theorem proving the expressiveness of search is often more important than
having a very fast search method, and thus worse performance is also not a big
drawback.

\subsection{Superclasses}

Like Scala's implicit design,\footnote{Note that, superclasses are often
simulated in Scala with OO Subtyping and class hierarchies, although there is
no one-to-one correspondence between both.} \name does not directly support
superclasses.  
% However, while superclasses are not directly supported, this
% does not mean that they cannot be encoded.
While superclasses can be encoded in \name, there are several problems.

% At first sight superclasses seem to rely on the ability to backtrack, as we may
% try to obtain a class directly or indirectly through one of its subclasses and
% apriori may not know which approach resolves transitively.
% Therefore an important question is whether the choice
% of committed choice precludes superclasses. 
% As we have argued in Section~\ref{sec:committed}, Haskell does not support
% backtracking either, and yet it supports superclasses. Although we do
% not cover superclasses in our work, and in particular in the
% (informally presented) encoding in Section~\ref{subsec:encoding}, it is possible to
% model superclasses even when the search strategy employs committed
% choice. Here we discuss superclasses in some more detail, and informaly
% discuss how superclasses can be integrated with a \name-like calculus.

\paragraph{Superclasses in Haskell}
Haskell has supported superclasses since the introduction of type classes. The
|Eq| and |Ord| classes, with |Eq| a superclass of |Ord|, constitute a standard example.
The following simplified code shows the two classes,
together with instances for integers:

> class Eq a where
>   (==) :: a -> a -> Bool
>
> class Eq a => Ord a where
>   (<) :: a -> a -> Bool
>
> instance Eq Int where dots
>
> instance Ord Int where dots

\noindent In the class context |Eq a| in the definition of the |Ord| class specifies
that |Eq a| is a superclass of |Ord a|.
Superclasses allow the use of methods from the superclasses, even if only the subclass
is part of the type class context. For example:

> p :: Ord a => a -> a -> Bool
> p = (==)     -- accepted because |Eq a| is a superclass of |Ord a|

\noindent Here the signature of function |p| assumes that an
instance for |Ord a| is available. In the body of |p|, the method |(==)| of the class |Eq a|
is used. This code is accepted in Haskell because |Eq a| is a superclass
of |Ord a|. 

\paragraph{Superclasses, Determinism and Coherence}
In the presence of superclasses, Haskell's resolution is not deterministic.
Consider this variant of |p|, defined
only for integers:

> p' :: Int -> Int -> Bool
> p' = (==)     

\noindent Haskell has two ways to resolve |Eq Int| to obtain the implementation
of |==| in |p'|. The first is to get the implementation of |Eq Int|
directly from the |Eq Int| instance. The second is to get an
implementation
of |Eq Int| as the superclass of |Ord Int|.
The two elaborations are
syntactically different, which makes elaboration
with Haskell superclasses non-deterministic. Nonetheless the elaboration is still
coherent, since both elaborations yield the same semantics (they both execute the
code of the one |Eq Int| instance).

% Haskell's resolution is non-determinsm is due to the fact that it does not order
% instance 
% An important difference with \name is that Haskell instances are unordered,
% whereas \name uses lexical scoping for implicits. Thus \name can be deterministic
% due to the ordering of the implicits in the context.

:%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{A First Attempt at Encoding Superclasses}
We can try to encode the previous Haskell definitions in then \name 
environment $\tenv = |?(forall a. Ord a => Eq a)|, |?(Eq Int)|, |?(Ord Int)|$, whose
implicit entries capture the superclass relation and the two instances.
With respect to \name, the query |?(Eq Int)| resolves deterministically by picking the second entry in $\tenv$.
Hence, \name's explicit ordering of implicits avoids Haskell's non-determinism.

% We would also be able to resolve the query |?(Eq Bool)| arising in the
% definition |p|, since the local context would be
% $\tenv_1 =$ |forall Bool. Ord Bool => Eq Bool, Eq Int, Ord Int, Ord Bool| and the superclass
% rule together with the last entry in the environment could then be used to conclude |Eq Bool|.

While the ordering is beneficial for determinism, fewer queries may succeed due to
an unsuitable order of implicits.
For example, suppose that we have instead the environment
$\tenv = |?(Eq Int)|, |?(forall a. Ord a => Eq a)|$, then resolving
|?(Eq Int)| fails
because the first entry matches and its requirement |Ord Int| cannot be satisfied. In this case the committed
choice semantics prevents reaching the second entry, which would resolve |Eq Int| directly.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Superclasses with Committed Choice}
The situation we just saw also arises in Haskell. Treating superclass relations
in the same way as type class instances does not work well with a committed
choice strategy. That is why GHC treats superclass relations differently. In
essence, whenever GHC adds a given type class constraint (e.g., from a
programmer-supplied type signature) to the type environment, it uses the
superclass relation to also add all of its ancestors. 
We believe that a similar strategy would be possible for \name. For instance,
in the last example, the type environment would be $\tenv = \envi{|Eq Int|}{x}$, not
contain the superclass relation and be able to resolve the query $|?(Eq Int)|$ with $x$. 
When adding an |Ord Int| entry, we would also add its |Eq Int| superclass, yielding the
modified environment $\tenv = \envi{|Eq Int|}{x}, \envi{|Ord Int|}{y}, \envi{|Eq Int|}{|super y|}$.
Now, the query |?(Eq Int)| is resolved with |super y|, which is the superclass value of the new |Ord Int|
entry.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Superclasses with Global Scoping and \name-style Resolution in GHC Haskell}
The newest version of GHC has a \name-inspired resolution algorithm in order to deal
with \emph{quantified class constraints}~\cite{}.\bruno{fill me in} 

But resolution in the presence of superclasses behaves differently from overlapping instances. 


\subsection{Coherence}

There are several ways to enforce coherence in a language design. For
example, Haskell guarantees coherence by ensuring that there is a
unique instance of a type class per type. In this way whenever code
accesses a type class dictionary, it always returns the same
(equal) dictionary value. This is a very strict way to enforce coherence.

\name's way to achieve coherence is more relaxed than Haskell's. \name
enforces that the elaboration and resolution are deterministic but,
under different scopes the same queries can resolve to different
values (unlike Haskell).

While determinism is sufficient to ensure
coherence, it is still a fairly strict way to ensure coherence. A
more relaxed and general notion of coherence is to allow elaboration
and resolution to have multiple different (but observationally equivalent)
terms for the same expression. Our Corollary~\ref{lem:coherence} provides a formal
statement of coherence that is based on contextual equivalence of two
expressions:

\[\forall \tenv, \rulet, E_1, E_2: \quad\quad 
     \dres{\tenv}{\rulet}{E_1} ~\wedge~ 
     \dres{\tenv}{\rulet}{E_2} \quad\Rightarrow\quad 
     \fctx{\etrans{\tenv}}{E_1}{E_2}{\ttrans[\rulet]} \]

This statement is close to the usual definition of coherence in the
literature~\cite{Reynolds91coherence,qual,BreazuTannen&91}.
That is, $E_1$ and $E_2$ are not required to be
syntactically equivalent, but they must be semantically equivalent.
Many language designs that are coherent are often not necessarily 
deterministic (unlike \name).

\begin{comment}
Finally, another possible alternative design would be not to have coherence
by construction, but still have some checks 
to ensure that when resolution happens there is a unique way to build
the implicit value for the respect query. For example,
with such an approach we could allow the implicit environment:
$\tenv =$ |Int, Bool, forall a. Bool => a, Char|, even though 
the query |?Int| would be ambiguous because there are two
possible possible ways to resolve the query. 
\end{comment}

\paragraph{Alternative Designs}
We use determinism to establish coherence in \name, but a more
relaxed notion of coherence would also be possible. For example if,
instead of committed choice, we decided to allow for a more powerful
resolution strategy (for example with backtracking), then a more
relaxed notion of coherence would be helpful. This could be useful
to deal with some situations that appear in superclasses.
For example, consider again the context
$\tenv =$ |?(Eq Int), ?(forall a. Ord a => Eq a), ?(Ord Int)|. In this
case the query |?(Eq Int)| can be resolved in two possible ways:
either going via the superclass instance |Ord Int|; or by directly
using the instance |Eq Int|. Even thought the two elaborations
are syntactically different, their semantics is the same. 


\begin{comment}
Coherence is indeed a fundamental question that has to be solved one way or
the other---and there are several ways to address this issue:
 - The solution chosen in COCHIS is to enforce a single elaboration term, by
   a deterministic resolution procedure, hence coherence follows by
   construction.
 - The Haskell solution is by enforcing uniqueness of dictionary values, so
   that whatever the code to access a dictionary, it will always return the
   same (equal) dictionary value.
 - One may allow multiple elaboration paths and show that all of them are
   observationally equivalent.  This can be a property holding by
   construction, as for example in "Inheritance as implicit coercion" by
   Breazu-Tannen, Coquand, Gunter, and Scedrov published in in Information
   and computation 93 (1), 172-221, which although in a different context
   (subtyping) was one of the first works to raise and emphasize the issue
   of coherence.
 - Coherence need not hold by construction: one would then check coherence
   for each implicit argument and reject the program if two possible
   elaborations cannot be proved observationally equivalent.
The paper does not sufficiently discuss this design space and in particular
the last option.  The presentation may even suggest (without explicitly
saying so) that there is no such option.  For example, the word coherence is
often used when determinism would be more appropriate.  Determinism implies
coherence, but not the converse.  Coherence is what is desired.  Determinism
is not a goal in itself.  On the opposite, more flexibility may be better,
for instance allowing for compiler optimization; it may also lead to a
simpler specification.
\end{comment}

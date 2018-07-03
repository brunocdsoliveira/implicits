%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Rule.fmt
%%include Scala.fmt
%format new = "\bf{new}"

%format === = "\cong"

\section{Discussion}\label{sec:discussion}

In the design of \name we had to take several design decisions. In
this section we discuss and justify several of those design decisions.
Mostly, many of these choices are motivated by the design of Haskell 
type classes or Scala implicits.

\bruno{Cite some of the papers that discuss various design options for Haskell?}


\subsection{Predicative Instantiation}

System F is an impredicative calculus, allowing the instantiation of
type variables with arbitrary (polymorphic) types. In contrast \name 
is predicative: instantiation of type
variables only allows \emph{monotypes}. The reason to depart from
traditional System F is due to three factors:

\begin{itemize}

\item {\bf Impredicative instantiation in resolution leads to additional
    ambiguity.} As discussed in Section~\ref{}, if instantiations of
  type variables during resolution are allowed to be impredicative,
  then additional ambiguity is possible. It is not obvious how to
  remove such ambiguity while retaining impredicativity. The
  restriction to predicative instantiation removes such ambiguity.

\item {\bf Impredicativity is complex when some implicit instantiation
  is allowed.} While traditional System F (where all type
instantiations are explicit) is simple, matters become much more
complicated when some implicit instantiation is allowed. Indeed the
design of System F-like calculi with implicit instantiation and/or
some form of type-inference is much more divided in terms of design
choices regarding (im)predicativity. One key complication has todo
with the most-general relation for implicit
polymorphism. The most-general relation allows systems with implicit 
polymorphism to decide whether a type is an instance of another type. 
For example the type |Int -> Int| is an instance of the polymorphic 
type |forall a . a -> a|. An algorithm for determining whether a type
is more general than another must perform implicit instantiation. 
Unfortunatelly it is well-known that for \emph{impredicative
  instantiation}, such most-general relation is undecidable~\cite{}. 
However, when only predicative instantiation is allowed, then 
the most-general relation is decidable~\cite{}. 
Resolution in \name is closely related to the most-general relation 
and we believe that, under impredicative instantiation, resolution is
indeed undecidable.\bruno{This may actually be a known result. See Rouvet?}

\item {\bf Predicative instantiation is not a big restriction in
    practice.} 
Due to the complications brought by impredicativity, many practical 
languages with type-inference only allow predicative instantiation.
For example, the key algorithm for type-inference currently employed 
by the GHC Haskell compiler is predicative~\cite{}. Other languages
with sophisticated forms of type-inference use similar
algorithms~\cite{}. Worth noting is that the original Hindley-Milner (HM)
system is where the predicativity restriction on polymorphic type
systems with type-inference was firstly put into place. 
Since \name is intended as a target for languages for languages with 
implicit polymorphism and type-inference, which often have
predicativity restrictions, restricting the core language to allow
predicative instantiation only is does not lose expressive power in practice.

\end{itemize}

\paragraph{Alternative Design Choices} One alternative design choice
worth mentioning for \name would be to allow impredicative
instantiation in type applications, but still retain the predicativity
restriction during resolution. This design would be less restrictive
than the design of \name, and we believe that it is a reasonable
design. We decided to also have the predicative instantiation even 
for the explicit type applications of \name for two reasons. Firstly, 
since \name is aimed to be a target for source languages with
type-inference, which often have predicative restrictions anyway, then 
there is not much to be gained by having impredicative instantiation
in the core. Secondly, and more importantly, some of the meta-theory
would be more involved if impredicative instantiation on type
applications was allowed. In particular, Lemma~\ref{} would need 
to be generalized to account for any types, rather than just
monotypes.

Allowing full impredicativity (both in type applications and
resolution) seems more complicated. We expect that such designs 
are possible, but necessaraly more complicated if ambiguity and
undecidability are to be avoided. We expect that the work on
impredicative type-inference~\cite{} is relevant, and perhaps some 
of the design choices employed in those works would be helpful 
in the design of a system with full impredicativity.  


\subsection{Committed Choice}

\name employs a committed choice for resolution. The motivation for
this choice is largely due to the strategy employed by Haskell. Since
early on it was decided that Haskell should not use backtracking
during resolution. When Haskell picks an instance it completely
ignores the context: only the head of the instance is considered in
resolution.  For example, consider the following program with
overlapping instances:

%format dots ="\ldots"

> class C a where
>   m :: a -> a
>
> instance Eq a => C [a] where
>   dots
>
> instance Ord a => C [a] where
>   dots
> 
> f :: StablePtr Int -> [StablePtr Int]
> f sp = m [sp] -- rejected!


\bruno{Is this a good example?}
In this piece of code we have a type class |C a| and two
instances. The first instance requires |Eq a|, whereas the second
instance requires |Ord a|. The function |f| takes a stable pointer
(|StablePointer|)
and returns a list of stable pointers. Notably |StablePointer| is a type
that supports equality, but not ordering. That is, there is an
instance |Eq (StablePointer a)| but not one for |Ord (StablePointer a)|. 

The question is should the above code type-check or not? In GHC
Haskell the answer is no.  Even though for this program there is no
ambiguity: the only choice is to pick the first type class instance,
the program is nevertheless rejected. The reason is that when
overlapping instances are used in Haskell, resolution only looks at
the head of the instances. In this case there are two equality specific
heads |C [a]| and therefore the program is rejected.

Although this design choice is not very well documented in the
research literature, the reason for not allowing backtracking is folklore among
Haskell programmers and can be found in documentation and
emails~\cite{}. In essence there are two argument for not allowing
backtracking during resolution:

\begin{itemize}

\item {\bf Reasoning:} When reasoning about Haskell code that involves
type classes, programmers often have to figure out which type class
instance is used. Essentially this requires recreating the steps
involved in the resolution algorithm. If only the heads are needed
to figure out which instances are used, then reasoning is relatively
simple. However when backtracking is involved then finding the instances
will require programmers to simulate the backtracking process, which
can be quite complex.

\item {\bf Performance:} Another strong motivation to disallow
backtracking is performance. If backtracking is allowed the compile
times required to type-check programs involving instances that require
alot of backtracking could grow exponentially. High compile times are
not desirable for programmers, therefore by disallowing backtracking
GHC eliminates a potential source of significant performance penalties
in type-checking.

\end{itemize}

\paragraph{Alternative Designs} Other implicit programming mechanisms
allow backtracking~\cite{}. Therefore another reasonable choice would
be to employ an algorithm that would perform backtracking as well. Allowing
backtracking has some advantages. For example more queries
would be accepted, and it would be possible to have a sound and complete
algorithm (instead of just a sound one) with respect to Figure~\ref{}.
In our work we opted by an algorithm that follows some of the practical considerations
that were discussed before in the Haskell community. The nearly 30 years
of experience with Haskell type classes indicate that such a choice works
reasonably well in practice. Nonetheless allowing backtracting does have
better properties in theory, and despite the practical disadvantages with
respect to committed choice, we think it is still a reasonable and worthwhile
design to explore in the context of programming languages. Indeed designs such as
Ocaml implicits~\cite{} are representative of such algorithms in practice.

In the context of theorem proving where
proof irrelevance is often in play having backtracking seems to be a better choice.
If type classes are building evidence for proofs, then proof irrelevance means
that it does not matter which concrete proof is found. What matters is that
some proof exists. In other words in this context coherence is not relevant,
and the objections about the difficulty of reasoning about which
instance is used is also not relevant. Then the only question is performance.
In theorem proving the expressiveness of search is often more important than
having a very fast search method, and thus performance is also not a big
drawback in such a setting.

\subsection{Superclasses}

Superclasses are not directly supported by \name. With respect to superclasses \name follows the design
of Scala implicits, which do not have a concept similar to
superclasses either\footnote{Note that, in Scala, superclasses are often
simulated with OO Subtyping and class hierarchies, although there
is not one-to-one correspondence between superclasses and OO hierarchies.}.
However, while superclasses are not directly supported, this does not mean
that they cannot be encoded.

At first sight superclasses seem to rely on the ability
to backtrack. Therefore an important question is whether the choice
of committed choice precludes superclasses. 
As we have argued in Section~\ref{}, Haskell does not support
backtracking either, and yet it supports superclasses. Although we do
not cover superclasses in our work, and in particular in the
(informally presented) encoding in Section~\ref{}, it is possible to
model superclasses even when the search strategy employs committed
choice. Here we discuss superclasses in some more detail, and informaly
discuss how superclasses can be integrated with a \name-like calculus.

\paragraph{Superclasses in Haskell}
Since the inception of type classes in Haskell that superclasses have
been supported.  A familiar example of superclasses is illustrated by
the classes |Eq| and |Ord| in Haskell, where |Eq| is a superclass of
|Ord|. The following simplified piece of code shows the two classes,
together with instances for integers:

> class Eq a where
>   (==) :: a -> a -> Bool
>
> class Eq a => Ord a where
>   (<) :: a -> a -> Bool
>
> instance Eq Int where
>   dots
>
> instance Ord Int where
>   dots

\noindent In the definition of the class |Ord| the type class constraint |Eq a| specifies
that |Eq a| is a superclass of |Ord a|.
Superclasses allow the use of methods from the superclasses, even if only a subclass
is part of the type class context. For example:

> p :: Ord a => a -> a -> Bool
> p = (==)     -- accepted because |Eq a| is a supertype of |Ord a|

\noindent In this case the type of the function |p| assummes that an
instance for |Ord a| exists. In the body of |p|, the method |==| (of the class |Eq a|)
is used. This code is accepted in Haskell because |Eq a| is a superclass
of |Ord a|. 

\paragraph{Superclasses and Overlapping} Consider the following variant of |p|, defined
only for integers:

> p' :: Int -> Int -> Bool
> p' = (==)     

\noindent This program is also accepted in Haskell. However, 
one important point about this example is that when finding the implementation
of |==| in |p| there are actually two possible ways to do so.
One option is to get the implementation of |Eq Int| directly from
the |Eq Int| instance. The other option is to get an implementation
of |Eq Int| from |Ord Int| via the superclass.

We can try to translate the Haskell program into \name by considering
the superclass relation as an additional rule of the form |forall a. Ord a => Eq a|.
However the corresponding \name program would not type-check.
In essence we appear to have a situation where we have a context similar to
$\tenv =$ |Eq Int, forall a. Ord a => Eq a, Ord Int|, and we have
to resolve the query |?(Eq Int)|. In \name however, the stability conditions
would prevent the program |p'| from type-checking under the context $\tenv$.



But resolution in the presence of superclasses behaves differently from overlapping instances. 

Superclasses have a ad-hoc treatement in GHC. 

\subsection{Coherence}

We use coherence as determinism in our paper. But, generally speaking, coherence can be interpreted
more broadly. 


 

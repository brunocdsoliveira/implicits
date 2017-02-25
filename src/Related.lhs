%include lhs2TeX.fmt
%include Scala.fmt
%include forall.fmt

\section{Related Work}
\label{sec:related}

This section discusses related work. The most closely related work can
be divided into three strands: IP mechanisms that support local
scoping with coherence, but forbid overlapping rules and lack other
types of flexibility; IP mechanisms that have global scoping and
preserve coherence; and IP mechanisms that are incoherent but offer
greater flexibility in terms of local scoping and/or overlapping
rules.  $\ourlang$ is unique in offering very flexible mechanisms
(including local scoping with overlapping rules, first-class rules 
and higher-order rules), while preserving coherence.

\subsection{Implicit Programming with Local Scoping, Coherence but no Overlapping Rules}
Our work allows a very flexible model of implicits with first-class
rules, higher-order rules and nested scoping with overlapping rules
while guaranteeing coherence.  Closest to our work in the goal of
combining additional flexibility with coherence are \emph{modular type
classes}~\cite{modular} and System $F_{G}$~\cite{systemfg}.  Both
works preserve coherence in the presence of local scoping, but (unlike
$\ourlang$) the local scopes \emph{forbid overlapping rules}. The
restriction of no overlapping rules is an essential part of
guaranteeing coherence. $\ourlang$ also has several other fundamental
differences to both modular type classes and System $F_{G}$.
\textit{Modular type classes}~\cite{modular} are a language design
that uses ML-modules to model type classes. The main novelty of this
design is that, in addition to explicit instantiation of modules,
implicit instantiation is also supported.  System
$F^{G}$~\cite{systemfg} also offers an implicit parameter passing
mechanism with local scoping, which is used for concept-based generic
programming~\cite{siek11concepts}. Both mechanisms are strongly influenced by type
classes, and they preserve some of the characteristics of type
classes: such only allowing modules or concepts to be implictly
passed. Moreover neither of those mechanisms support higher-order
rules. In contrast $\ourlang$ follows the Scala implicits phylosophy
and allows values of any type to be implicit, and additionally
higher-order rules are supported.

There have been also some proposals for addressing the limitations that
arise from global scoping~\cite{named_instance,implicit_explicit} in type classes.
However in those designs, type classes are still second-class and
resolution only works for type classes.\bruno{say more: not formally studied; 
unclear if coherence holds?}

\emph{Implicit parameters}~\cite{implicit_param} are a proposal for a
name-based implicit parameter passing mechanism with local scoping. 
Implicit parameters allow \emph{named}
arguments to be passed implicitly, and these arguments can be of any
type. However, implicit parameters do not support recursive resolution,
so for most use-cases of type-classes, including the |Ord| instance 
for pairs in Section~\ref{subsec:tclasses}, implicit parameters would be very cumbersome. They 
would require manual composition of rules, instead 
of relying on the recursive resolution mechanism to do this automatically.
This in in stark contrast with most other IP mechanims, including $\ourlang$, 
where recursive resolution and the ability to compose rules automatically is 
a key feature and source of convinience.

\subsection{Implicit Programming with Coherence and Global Scoping}

Several core calculi and refinements have been proposed in the context
of type-classes. As already discussed in detail in
Section~\ref{sec:intro}, there are a number of design choices that
(Haskell-style) type classes take that are different from $\ourlang$. 
Most prominently, type classes make a strong differentiation
between types and type classes, and they use global scoping instead of
local scoping for instances/rules. The design choice for global scoping can be
traced back to Wadler and Blott's~\shortcite{adhoc} original paper on
type classes. They wanted to extend Hindley-Milner
type-inference~\cite{hindley69principal,milner78theory,damas82principal}
and discovered that local instances resulted in the loss of principal
types. For Haskell-like languages the preservation of principal types 
is very important, so local instances were discarded. 
However, there are many languages with IP
mechanisms (including Scala, Coq, Agda, Idris or Isabelle) that have more
modest goals in terms of type-inference. In these languages there are
usually enough type annotations that ambiguity introduced by local instances 
is avoided, and there is indeed added expressive power because type 
annotations drive the resolution process.

Jones's work on \emph{qualified types}~\cite{simpl_qual} provides a
particularly elegant framework that captures type classes and other
forms of predicates on types. Like type classes, qualified types too
make a strong distinction between types and predicates over types, and
scoping is global. Jones~\shortcite{coherence_qual} discusses the
coherence of qualified types. The formal statement of coherence in $\ourlang$
is similar to the one used in qualified types.\bruno{double-check that this is true.} 

\begin{comment}
 In his definition, the translation
semantics is coherent if the given system of predicates guarantees the
uniqueness of evidence. This notion of coherence provides a general
framework for Haskell-like systems, but it leaves out the details of
how to coherently generate the evidence, which is non-trivial with
overlapping instances.
\end{comment}

The GHC Haskell compiler supports overlapping
instances~\cite{designspace}, that live in the same global scope. This
allows some relief for the lack of local scoping, but it still does 
not allow different instances for the same type to coexist in 
different scopes of a program.
$\ourlang$ has a different approach to overlapping compared to
\emph{instance chains}~\cite{chain}. With instance chains the
programmer imposes an order on a set of overlapping type class
instances. All instance chains for a type class have a global scope and
are expected not to overlap. This makes the scope of overlapping
closed within a chain.  In our calculus, we make our local scope
closed, thus overlap only happens within one nested scope.
More recently, there has been a proposal for \emph{closed type families 
with overlapping equations}~\cite{eisenberg}. This proposal allows the
declaration of a type family and a (closed) set of instances. 
After this declaration no more instances can be added. In contrast 
our notion of scoping is closed at a particular resolution point, but 
the scopes can still be extended in other resolution
points.

A lot of
work on type classes is focused on increasingly more powerful ``type
class'' interfaces.  \emph{Functional dependencies}~\cite{fundeps},
\emph{associated types}~\cite{assoctypes,assoctypes2} and \emph{type
  families}~\cite{typefunc} are all examples of this trend.  This line
of work is orthogonal to our own.


\subsection{Implicit Programming without Coherence}

\paragraph{Implicit calculus}

The main inspiration for our work comes from Scala
implicits~\cite{implicits,scala}. Like our work Scala implicits allow
implicit parameters of any types of values and recursive resolution is
supported.

Therefore there are noteworthy differences between $\ourlang$ and
Scala implicits. In contrast to $\ourlang$, Scala has subtyping. We do
not think that subtyping is essential, and it complicates the
formalization: as discussed in Section~\ref{subsec:extensions}
subtyping would require considerable adaptations to our calculus.
Therefore we have omitted subtyping here.  Although Scala also
provides local and nested scoping, nested scoping can only happen
through subclassing and the rules for resolution in the presence of
overlapping instances are quite ad-hoc.
In other words Scala's scoring system attempts to account 
for both nested scoping through subclassing and the most specific type, whereas in the 
implicit calculus only the lexical scope is considered.
Finally, Scala has no (first-class) rule abstractions and
consequently no support for higher-order rules. Rather,
implicit arguments can only be used in definitions. 

However, Scala does not provide coherence
checking and, as such, it is possible to incoherently select rules
in the presence of nested scoping. Figure~\ref{fig:scala} illustrates
the issue briefly, using the example that was presented in
Section~\ref{sec:intro}. Scala's subclassing creates nested
implicit scopes. The program is accepted, but Scala incoherently
selects the more general implicit value (|id|) for |v1|. In contrast, |v2|,
which inlines |func[Int]|, picks |succ|. As a result, despite
looking equivalent, the two expressions yield different results.
Finally, Scala implicits do not allow higher-order rules and queries;
and the mechanism is only informally described.

\paragraph{IP Mechanisms in Dependently Typed Programming}

A number of dependently typed languages also include several
mechanisms inspired by type classes. Although such mechanisms 
have been implemented and they are actively used, there is little 
work on formalization. 

\paragraph{Isabelle Type Classes} The first type-class mechanism 
in a theorem prover was in Isabelle~\cite{haftmann06constructive}. The mechanism was 
largely influenced by Haskell type classes and shares many of the 
same design choices. The introduction of \emph{axiomatic type classes}~\cite{wenzel00usingaxiomatic} 
showed how theorem proving can benefit from type classes to model 
not only the operations in type classes, but also the corresponding
algebraic laws. 

\paragraph{Coq's Canonical Structures And Type Classes}
The Coq theorem prover has two mechanisms that allow modelling
type-class like structures: \emph{canonical structures}~\cite{gonthier11lessad-doc} and
\emph{type classes}~\cite{coqclasses}. The two mechanisms have quite a bit of
overlap in terms of functionality. In both mechanisms the idea is to
use dependent records to model type-class-like structures, and pass
instances of such records implicitly. Both mechanisms support
recursive resolution to automatically build suitable records and they
follow Haskell type classes model of global scoping.
Furthermore, because Coq is dependently typed an additional feature of
the two mechanisms is that they can also model \emph{value
  classes}~\cite{gonthier11lessad-doc} (that is classes parametrized by values, rather
than by types). This functionality is not available in the implicit
calculus, due to the lack of dependent types.  Another difference is
that recursive resolution is allowed to backtrack in canonical
structures and type classes, whereas the implicit calculus forbids
this. The reason for forbidding backtracking in the implicit calculus
(and also Haskell type classes) is justified by the use of the
mechanism for programming purposes, and the need for users to
easily predict which instances are used. In a theorem proving context,
backtracking makes more sense since, due to \emph{proof irrelevance},
which instances get picked in a proof is not so important, as long as the
proof is completed.

A key difference to our work is that both canonical structures and
Coq's type classes focus on the implementation of a concrete
mechanism, whereas we focus on the formalization of a general
mechanism.  Neither canonical structures nor Coq's type classes have
been formally specified. It could be that a generalization of the
implicit calculus with dependent types (and allowing backtracking)
would be able to provide a suitable specification for these
mechanisms. Generalizing the implicit calculus with Coq style
dependent types poses considerable challenges, because computation
can happen during type-checking.

\emph{Instance arguments}~\cite{instanceargs} are an Agda extension
that is closely related to implicits. Like the implicit calculus, 
instance arguments use a special arrow for introducing implicit 
arguments. However, unlike most other mechanisms,
implicit rules are not declared explicitly. Instead rules are drawn
directly from the type-environment, and any previously defined 
declaration can be used as a rule. 
Furthermore resolution is limited in its expressive power, to avoid
introducing a different computational model in Agda. This design
differs significantly from $\ourlang$, where resolution is very
expressive and the scoping mechanisms allow explicit rule declarations.

Rules in $\ourlang$ can  also  be
first-class implicit functions, but unlike instance arguments we 
can express higher-order rules. 

\subsection{Global Uniqueness and Same Instance Guarantee}
Liskov

\subsection{Focused Proof Search}
\bruno{Tom, this is for you to fill in.}



%-------------------------------------------------------------------------------
\subsection{Power of Resolution}
\tom{Moved here from Section 3.}
\tom{TODO: Do we still need this to appear here for the conference paper? Is
it even still true with all the determinism and coherence enforcement?}

The rules for deterministic resolution presented in this paper support all the
examples described in Section~\ref{sec:overview}. They are strictly more powerful than
the rules presented in the conference version of the paper~\cite{oliveira12implicit}.
In other words, strictly more queries resolve with this article's rules than
with the rules of the previous paper.
For example, 
the query:

\begin{equation*}
  \tychar \To \tybool,
  \tybool \To \tyint \vturns \tychar \To \tyint
\end{equation*}

\noindent does not resolve under the deterministic resolution rules of
the conference paper. In order to resolve such rule types, it is 
necessary to add the rule type's context to the implicit
environment in the course of the resolution process: 

\begin{equation*}
  \tychar \To \tybool,
  \tybool \To \tyint, \tychar \vturns \tyint
\end{equation*}

\noindent but this was not supported by our previous set of rules. The new set
of resolution rules do support this by means of rule \RIAbs, and queries like
the above can now be resolved.

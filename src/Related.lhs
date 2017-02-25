%include lhs2TeX.fmt
%include Scala.fmt
%include forall.fmt

\section{Related Work}
\label{sec:related}

This section discusses related work. The most closely related work can be divided 
into two parts: IP mechanisms that support coherence, but lose some flexibility; 
and IP mechanisms that are incoherence but offer greater flexibility. $\ourlang$
is unique in offering very flexible mechanisms, while ensuring coherence. 

Our work allows nested scoping with overlapping rules while guaranteeing
coherence. Regarding these issues, previous approaches can be divided into two
kind. The first kind allows local scoping but forbids nested scoping and, as
such, avoids the issue of guaranteeing coherence in the presence of
overlapping. Modular type
classes~\cite{modular} and System $F_{G}$~\cite{systemfg} are examples of
this kind of approach. The second kind allows nested scoping,
but does not guarantee coherence. Most prominently Scala falls in this
category, but there are several other proposals that also follow this
approach~\cite{systemct,implicit_explicit,instanceargs}.

\subsection{Implicit Programming with Coherence}
Several core calculi and refinements have been proposed in the context
of type-classes. As already discussed in detail in
Section~\ref{sec:intro}, there are a number of design choices that
(Haskell-style) type classes take that are different from the implicit
calculus. Most prominently, type classes make a strong differentiation
between types and type classes, and they use global scoping instead of
local scoping for the rule environment. These design choices can be
traced back to Wadler and Blott's~\shortcite{adhoc} original paper on
type classes.  The reason for global scoping is also motivated by
Wadler and Blott. They wanted to extend Hindley-Milner
type-inference~\cite{hindley69principal,milner78theory,damas82principal}
and discovered that local instances resulted in the loss of principal
types.  However, there are many languages with type-class like
mechanisms (including Scala, Coq, Agda and Isabelle) that have more
modest goals in terms of type-inference.  In these languages there are
usually enough type annotations that such ambiguity is avoided, and
there is indeed added expressive power because type annotations drive
the resolution process.

There is a wide range of work that builds on the original type
classes proposal~\cite{adhoc}. Jones's work on \emph{qualified
  types}~\cite{simpl_qual} provides a particularly elegant framework
that captures type classes and other forms of predicates on
types. Like type classes, qualified types too make a strong
distinction between types and predicates over types, and scoping is
global. There have been some proposals for addressing the limitations
that arise from global
scoping~\cite{named_instance,implicit_explicit}.  However in those
designs, type classes are still second-class and resolution only works
for type classes. The GHC Haskell compiler supports overlapping
instances~\cite{designspace}, that live in the same global scope. This
allows some relief for the lack of local scoping.  A lot of recent
work on type classes is focused on increasingly more powerful ``type
class'' interfaces.  \emph{Functional dependencies}~\cite{fundeps},
\emph{associated types}~\cite{assoctypes,assoctypes2} and \emph{type
  families}~\cite{typefunc} are all examples of this trend.  This line
of work is orthogonal to our own.

Our calculus has a different approach to overlapping compared to
\emph{instance chains}~\cite{chain}. With instance chains the
programmer imposes an order on a set of overlapping type class
instances. All instance chains for a type class have global scope and
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

Our calculus is different from \emph{instance chains}~\cite{chain}
too. With instance chains the programmer imposes an
order on a set of overlapping type class instances. All instance
chains for a type class have global scope and are expected not to
overlap. This makes the scope of overlapping closed within a chain,
which is one way to ensure the coherence under the presence of
overlap. In our calculus, we make our local scope closed,
thus overlap only happens within one nested scope.

Lastly, Jones~\shortcite{coherence_qual} discusses the coherence of
qualified type systems in his work on qualified types. In his
definition, the translation semantics is coherent if the given
system of predicates guarantees the uniqueness of evidence. This
notion of coherence
provides a general framework for Haskell-like systems, but it leaves
out the details of how to coherently generate the evidence, which
is non-trivial with overlapping instances.


\emph{Implicit parameters}~\cite{implicit_param} are a proposal for a
name-based implicit parameter passing mechanism with local scoping. Lewis et al.
formalized a small core language with the mechanism and there is also
a GHC Haskell implementation. Implicit parameters allow \emph{named}
arguments to be passed implicitly, and these arguments can be of any
type. However, implicit parameters do not support recursive resolution,
so for most use-cases of type-classes they require composing 
rules manually, instead of relying on the recursive resolution 
mechanism to do this automatically.

\paragraph{System $F^{G}$} System $F^{G}$~\cite{systemfg} also offers an implicit 
parameter passing mechanism with local scoping, which is used
for concept-based generic programming. 
Instead of a name-based approach, a type-directed approach is used
for passing implicit parameters. This is closer to $\ourlang$ than implicit parameters.
A more important difference to the implicit calculus is that, like type classes, there is a
strong differentiation between types and concepts
in System $F^{G}$:
concepts cannot be used as types; and types cannot be used as
concepts. As a consequence, models implementing concepts can only 
be passed as implicit parameters, and regular values can only be
passed as explicit parameters. 


\textit{Modular type classes}~\cite{modular} are a language design
that uses ML-modules to model type classes.  The main novelty of this
design is that, in addition to explicit instantiation of modules,
implicit instantiation is also supported. In this design local scoping is
allowed. However, unlike $\ourlang$ (and also System
$F^{G}$ and implicit parameters) the local scopes cannot be nested.
Furthermore, implicit instantiation is limited to modules (that is 
other regular values cannot be implicitly passed and automatically resolved).
Finally System $F^{G}$ only formalizes a very simple
type of resolution, which does not support recursive resolution. 

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

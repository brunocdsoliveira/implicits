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
rules.  $\ourlang$ is unique in offering flexibility 
(local scoping with overlapping rules, first-class rules 
and higher-order rules), while preserving coherence.

\subsection{Implicit Programming with Local Scoping, Coherence but no Overlapping Rules}
Our work allows a very flexible model of implicits with first-class
rules, higher-order rules and nested scoping with overlapping rules
while guaranteeing coherence.  Closest to our work in terms of
combining additional flexibility with coherence are \emph{modular type
classes}~\cite{modular} and System $F_{G}$~\cite{systemfg}. Both 
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
classes such as only allowing modules or concepts to be implicitly
passed. Moreover neither of those mechanisms support higher-order
rules. In contrast $\ourlang$ follows the Scala implicits philosophy
and allows values of any type to be implicit, and additionally
higher-order rules are supported.

\emph{Implicit parameters}~\cite{implicit_param} are a proposal for a
name-based implicit parameter passing mechanism with local scoping. 
Implicit parameters allow \emph{named}
arguments to be passed implicitly, and these arguments can be of any
type. However, implicit parameters do not support recursive resolution,
so for most use-cases of type-classes, including the |Ord| instance 
for pairs in Section~\ref{subsec:tclasses}, implicit parameters would be very cumbersome. They 
would require manual composition of rules instead 
of providing automatic recursive resolution.
This is in stark contrast with most other IP mechanisms, including $\ourlang$, 
where recursive resolution and the ability to compose rules automatically is 
a key feature and source of convenience.

\subsection{Implicit Programming with Coherence and Global Scoping}

Several core calculi and refinements have been proposed in the context
of type classes. As already discussed in detail in
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
usually enough type annotations such that ambiguity introduced by local instances 
is avoided.

There have been some proposals for addressing the limitations that
arise from global scoping~\cite{named_instance,implicit_explicit} in the context 
of Haskell type classes. Both \emph{named instances}~\cite{named_instance} and 
\emph{Explicit Haskell}~\cite{implicit_explicit} preserve 
most design choices taken in type clases (including global scoping), 
but allow instances that not participate in the 
automatic resolution process to be named. This enables the possibility of overriding 
the compiler's default resolution result with a user-defined choice.

Jones's work on \emph{qualified types}~\cite{simpl_qual} provides a
particularly elegant framework that captures type classes and other
forms of predicates on types. Like type classes, qualified types
make a strong distinction between types and predicates over types, and
scoping is global. Jones~\shortcite{coherence_qual} discusses the
coherence of qualified types. The formal statement of determinacy in $\ourlang$
essentially guarantees a strong form of coherence similar to the one used in qualified types. 

\begin{comment}
 In his definition, the translation
semantics is coherent if the given system of predicates guarantees the
uniqueness of evidence. This notion of coherence provides a general
framework for Haskell-like systems, but it leaves out the details of
how to coherently generate the evidence, which is non-trivial with
overlapping instances.
\end{comment}

The GHC Haskell compiler supports overlapping
instances~\cite{designspace} that live in the same global scope. This
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
the scopes can still be extended at other resolution
points.

\begin{comment}
A lot of
work on type classes is focused on increasingly more powerful ``type
class'' interfaces.  \emph{Functional dependencies}~\cite{fundeps},
\emph{associated types}~\cite{assoctypes,assoctypes2} and \emph{type
  families}~\cite{typefunc} are all examples of this trend.  This line
of work is orthogonal to our own.
\end{comment}

\subsection{Implicit Programming without Coherence}

\paragraph{Implicits} The implicit calculus~\cite{oliveira12implicit} is the main 
inspiration for the design of $\ourlang$. There are two major 
differences between $\ourlang$ and the implicit calculus. 
The first difference is that the implicit calculus, like Scala, 
does not enforce coherence. Programs similar to that in Figure~\ref{fig:scala}
can be written in the implicit calculus and there is no way to detect 
incoherence. The second difference is in the design of resolution. 
Rules in the implicit calculus have $n$-ary arguments, whereas 
in $\ourlang$ rules have single arguments and $n$-ary arguments
are simulated via multiple single argument rules. The resolution process 
with $n$-ary arguments in the implicit calculus is simple, but quite ad-hoc 
and forbids certain types of resolution that are allowed in $\ourlang$. For example,
the query:
\begin{equation*}
  \tychar \To \tybool,
  \tybool \To \tyint \vturns \tychar \To \tyint
\end{equation*}

\noindent does not resolve under the deterministic resolution rules of
the implicit calculus, but it resolves in $\ourlang$. Essentially
resolving such query requires adding the rule type's context to the
implicit environment in the course of the resolution process. But in
the implicit calculus the implicit environment never changes during
resolution, which significantly weakens the power of resolution.
\emph{Scala implicits}~\cite{implicits,scala} were themselves the
inspiration for the implicit calculus and, therefore, share various
similarities with $\ourlang$.  In Scala implicit arguments can be of
any type, and local scoping (including overlapping rules) is
supported. However Scala implicits are incoherent and they do not
allow higher-order rules either.

\paragraph{IP Mechanisms in Dependently Typed Programming}
A number of dependently typed languages also have IP mechanisms
inspired by type classes. Coq's type classes~\cite{coqclasses} and
canonical structures~\cite{gonthier11lessad-doc}, Agda's instance
arguments~\cite{instanceargs} and Idris type classes~\cite{brady} all allow multiple and/or highly overlapping
rules/instances that can be incoherent. 
The Coq theorem prover has two mechanisms that allow modelling
type-class like structures: \emph{canonical structures}~\cite{gonthier11lessad-doc} and
\emph{type classes}~\cite{coqclasses}. The two mechanisms have quite a bit of
overlap in terms of functionality. In both mechanisms the idea is to
use dependent records to model type-class-like structures, and pass
instances of such records implicitly, but they still follow Haskell's 
global scoping approach. Nevertheless highly overlapping instances, which 
can be incoherent, are allowed. Like implicits, the design of
Idris type classes allows for any type of value to be implicit. Thus
type classes in Idris are first-class, can be manipulated as any other 
value, an also allow multiple (incoherent) instances of the same type.
\emph{Instance arguments}~\cite{instanceargs} are an Agda extension
that is closely related to implicits. Like $\ourlang$, 
instance arguments use a special arrow for introducing implicit 
arguments. However, unlike most other mechanisms,
implicit rules are not declared explicitly. Instead rules are drawn
directly from the regular type environment, and any previously defined 
declaration can be used as a rule. The original design of instance arguments
severely restricted the power of resolution by forbidding recursive resolution.
Since then, recursive resolution has been enabled in Agda. Like Coq's and Idris's 
type classes, instance arguments allow multiple incoherent rules.

\begin{comment}
An interesting aspect about IP mechanisms for theorem proving is that,
in such a context, incoherence is less dangerous. Due to
\emph{proof irrelevance}, which instances get picked in a proof is not
so important, as long as a proof exists.
\end{comment}

\subsection{Global Uniqueness and Same Instance Guarantee}
Haskell type classes not only ensure coherence
but also \emph{global uniqueness}~\cite{uniqueness} (due to global scoping), as discussed in
Section~\ref{sec:overview-coherence}. Unrestricted $\ourlang$ programs ensure coherence
only, as multiple rules for the same type can coexist in the same
program. We agree that for programs such as the |Set| example, it is
highly desirable to ensure that the same ordering instance is used
consistently. $\ourlang$ is a core calculus, meant to enable the
design of source languages that utilize its power. It should be easy
enough to design source languages on top of $\ourlang$ that forbid
local scoping constructs and, instead, make all declared rules visible
in a single global environment. This would retain several of
benefits of $\ourlang$ (such as first-class, higher-order rules, and
coherent overlapping rules), while providing a form of global
uniqueness. However this design would still be essentially
non-modular, which is a key motivation for many alternatives to type
classes to provide local scoping instead. 

Global uniqueness of instances is just a sufficient property to ensure
consistent uses of the same instances for examples like |Set|. However,
the important point is not to have global uniqueness, but to consistently use the same instance.  $\ourlang$
admittedly does not provide a solution to enforce such
consistency, but there is existing work with an alternative solution to deal with the problem. Genus~\cite{Zhang15LFO}
tracks the types of instances to enforce their consistent use.
For instance, in Genus two sets that use different orderings
have different types that reflect which 
|Ord| instance they use. As a consequence, taking the union of those two sets is
not possible.  In contrast to $\ourlang$ Genus is focused on providing
a robust source language implementation for generic
programming. Although the Genus authors have proved some meta-theoretic results,
neither type-safety nor coherence have been proved for Genus.  In
dependently typed languages such as Agda and Idris, it is possible to
parametrize types by the instances they use~\cite{brady}. This
achieves a similar outcome to Genus's approach to consistent usage of
instances. Investigating the applicability of a similar approach to 
$\ourlang$ is an interesting line of future work.

\subsection{Focused Proof Search}
% \paragraph{Similarity with Focused Proof Search}
Part of the syntax-directedness of our deterministic resolution is very similar
to that obtained by \emph{focusing} in proof
search~\cite{focusing,Miller91b,Liang:2009}. Both approaches alternate a phase
that
is syntax directed on a ``query'' formula (our first auxiliary judgement),
with a phase that is syntax directed on a given formula (our third auxiliary
judgement). This is as far as the correspondence goes though, as the choice
of given formula to focus on is typically not deterministic in focused proof
search.

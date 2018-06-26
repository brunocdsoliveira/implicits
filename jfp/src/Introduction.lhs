%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Rule.fmt
%include Scala.fmt

%format a = "\alpha"
%format b = "\beta"

\newcommand{\Meta}[1]{{\it #1\/}}
\newcommand{\m}[1]{\ensuremath{#1}}

\newcommand{\qlam}[2]{\m{\lambda\{#1\}.#2}}
\newcommand{\qask}[1]{\m{\Meta{?}#1}}
\newcommand{\qapp}[2]{\m{(#1)\;\texttt{with}\;#2}}
\newcommand{\qlet}[2]{\texttt{implicit}\;#1\;\texttt{in}\;#2}
\newcommand{\qLam}[2]{\m{\Lambda#1.#2}} 
  
\newcommand{\ty}[1]{\Meta{#1}}
\newcommand{\tyInt}{\Meta{int}}
\newcommand{\tyBool}{\Meta{bool}}
\newcommand{\rulety}[2]{\m{\{#1\}\!\Rightarrow\!#2}}

\section{Introduction}
\label{sec:intro}

%%* Implicit programming
%%* Type classes, C++ concepts, Scala implicits, JavaGI
%%* resolution, type-based

Programming language design is usually guided by two, often conflicting, 
goals: \emph{flexibility} and \emph{ease of reasoning}.
Many programming languages aim at providing powerful, 
flexible language constructs that allow programmers to achieve reuse, 
and develop programs rapidly and concisely. Other programming languages aim 
at easy reasoning about programs, as well as at avoiding programming
pitfalls. Often the two goals are at odds with each other, since 
highly flexible programming mechanisms make reasoning harder. 
Arguably the art of programming language design is to reconcile
both goals. 

A concrete case where this issue manifests itself is in the design of
\emph{Implicit Programming} (IP) mechanisms.
Implicit programming denotes a class of language mechanisms,
which infer values by using type information. Examples of IP
mechanisms include Haskell's type classes~\cite{adhoc}, C++'s
concepts~\cite{concepts}, JavaGI's generalized interfaces~\cite{javagi}, Coq's type
classes~\cite{coqclasses}, Scala's
implicits~\cite{scala}, Agda's \emph{instance arguments}~\cite{instanceargs}, Rust's \emph{traits}~\cite{rust}, and OCaml's \emph{modular implicits}~\cite{DBLP:journals/corr/WhiteBY15}. IP can also be viewed as a form of
(type-directed) program synthesis~\cite{Manna:1980:DAP:357084.357090}. The programming is said to
be \emph{implicit} because expressions (e.g., those for function
parameters) can be omitted by the programmer. Instead the necessary values are
provided automatically via a \emph{type-directed resolution} process. 
These implicit values are either fetched by type from the current (implicit)
environment or constructed by type-directed rules.

Currently there are two main schools of thought regarding the design
of IP mechanisms. Haskell's type classes~\cite{adhoc} embody the first
school of thought, which is guided by the \emph{ease of reasoning}
qualities of pure functional languages, and the \emph{predictability}
of programs. To ensure these goals the semantics of the language
should satisfy a number of properties. One of those properties is
\emph{coherence}~\cite{Reynolds91coherence,qual}.  The original
definition of coherence in the literature is that any valid program
must have exactly one meaning (that is, the semantics is not
ambiguous). 
In fact Haskell type classes are supposed to support an even stronger
property, the so-called \emph{global uniqueness} of
instances~\cite{uniqueness}.  Global uniqueness ensures that \emph{at
  any point in a program, and independently of the context} the
type-directed resolution process always returns the same value for the
same resolved type. This is a consequence of Haskell having a
restriction of at most one instance of a type class per type in a
program.

While both coherence and global uniqueness of instances are preserved in Haskell,
this comes at a cost. Since the first implementations of type classes,
Haskell imposes several restrictions to guarantee those properties. 
Various past work has pointed out limitations of type classes~\cite{named_instance,systemct,implicit_explicit,modular,Garcia:2007extended,implicits,chain,oliveira12implicit}. 
In particular type classes allow at most one instance per type (or severely 
restrict overlapping instances) to exist in a program. This means  
that all instances must be visible globally, and local scoping of
instances is not allowed. 
This form of global scoping goes against 
modularity. Other restrictions of type classes are 
that they are not first-class values and that the type-directed rules 
cannot be higher-order~\cite{oliveira12implicit}. 

Advanced
features of type classes, such as overlapping
instances~\cite{overlapping_instances},
also pose severe problems, since they go against the principle 
of one instance per type. One issue is that ``\emph{when more specific overlapping
instances are added, the proofs of some predicates will change to use
the new instances}''~\cite{chain}. In essence special care (via restrictions) is needed to preserve
coherence in the presence of overlapping instances. 
% In purely functional programming,
% ``\emph{substituting equals for equals}'' is expected to hold. That is,
% when given two equivalent expressions, replacing one by the other in a larger program
% always leads to two programs that yield the same
% result. 
% Special care (via restrictions) is needed to preserve
% coherence and the ability of substituting equals for equals in the
% presence of overlapping instances. 
Another important property
that is broken in the presence of overlapping instances 
(if special care is not taken) is the so-called \emph{stability} of
substitutions. The issue is that 
the behaviour of resolution for an expression |e| can change if |e| 
gets a more specific type, leading to a different evaluation result. 
This is problematic because seemingly harmless inlinings 
will actually have a different semantics before and after the inlining.
Because of this problem, the design of Haskell type classes
significantly restricts the set of valid overlapping instances to ensure 
that stability holds, and the meaning of an expression does not change 
simply due to a more specific type. In other words, resolution 
should resolve implicit values using the same rules before 
and after instantiation of type variables.

As an orthogonal remark, in the Haskell community, the term coherence
is often colloquially used to encompass several different properties,
including global uniqueness, stability and the original coherence
definition by Reynolds~\cite{Reynolds91coherence}. However it is
important to note that the three properties are distinct. For example
global uniqueness implies coherence, but not the converse.
Furthermore it is also possible to have coherence, but not stability.
In this paper we will use coherence in Reynolds' sense, and be precise 
about the different properties under discussion.

An alternative school of thought in the design of IP mechanisms favours \emph{flexibility}. For example, 
Scala's implicits and Agda's instance arguments do not impose all of
the type class restrictions. Scala supports local scoping of
instances, which allows distinct 
instances to exist for the same type in different scopes of the same
program. Scala also allows a powerful form of overlapping 
implicits~\cite{implicits}. The essence of this style of implicit
programming is modelled by the \emph{implicit
  calculus}~\cite{oliveira12implicit} or the more recent SI calculus~\cite{odersky17implicits}. The implicit 
calculus supports a number of features that are not supported 
by type classes. Besides local scoping, in the implicit calculus 
\emph{any type} can have an implicit value. In contrast Haskell's type
class model only allows instances of classes (which can be viewed 
as a special kind of record) to be passed implicitly. Finally the
implicit calculus supports higher-order instances/rules: 
that is rules, where the rule requirements can themselves be other rules. 
The
implicit calculus has been shown to be type-safe, and it also ensures
coherence, but it lacks stability. The SI calculus lacks both
coherence and stability, but the authors present a simply-typed subset 
that is coherent\footnote{It makes no sense to talk about stability
  in a simply typed calculus, since this is a property that is only
  relevant for polymorphic calculi.}.
Unfortunately, while both the implicit/SI calculus and the various existing
language mechanisms embody flexibility, the lack of
important properties such as stability makes reasoning about the
semantics of programs harder, and can prevent refactorings and 
compiler optimizations such as inlining. 

The design of IP mechanisms has led to heated
debate~\cite{show-stopping,uniqueness,kmett} about the
pros and cons of each school of thought: ease of reasoning versus
flexibility. Proponents of the Haskell school of thought argue that
having coherence, stability and uniqueness of instances is extremely desirable, and flexibility should not
come at the cost of those properties. Proponents of flexible IP
mechanisms argue that flexibility is more important, and that
uniqueness of instances goes against modularity. 
As far as we are aware there are no current designs that support local scoping,
overlapping instances and various other features, such as first-class and
higher-order rules, while at the same time also ensuring both coherence and
stability.
%%The current
%%state-of-affairs seems to indicate that both goals are at odds with
%%each other, and cannot be easily reconciled.
%% \footnote{Cochise, 1804--1874, was chief of the Chokonen band of
%%      the Chiricahua Apache.}

This paper presents \name: the Calculus Of CoHerent ImplicitS. \name
is an improved variant of the implicit calculus that guarantees 
\emph{coherence} and \emph{stability}. \name supports local scoping, overlapping instances,
first-class instances and higher-order rules. Yet, in contrast to most
previous work that supports these features, the calculus is not only
type-safe, but also stable and coherent. Naturally, the unrestricted calculus
does not support global uniqueness of instances, since this property depends on the
global scoping restriction. Nevertheless, if retaining global
uniqueness is desired, that can be modeled by the subset of
\name without local declarations.
%If a single global scope exists in a
%program then the determinism and coherence of \name imply that 

Ensuring coherence and stability in the presence of \name's overlapping and
higher-order rules is particularly challenging.
We introduce a logical formulation of how to resolve implicits, which
is simple but ambiguous and incoherent, and a second formulation,
which is less simple but unambiguous and coherent.  Every resolution
of the second formulation is also a resolution of the first, but not
conversely.  Parts of the second formulation bear a close resemblance
to a standard technique for proof search in logic called
\emph{focussing}~\cite{focusing,Miller91b,Liang:2009}. However, unlike
focused proof search, which is still essentially non-deterministic,
\name's resolution employs additional techniques to be entirely
deterministic and coherent.  In particular, unlike focused proof
search, our resolution uses a stack discipline to prioritize rules,
and removes any recursive resolutions from matching decisions. Moreover,
further restrictions are needed to obtain stability.

In summary, our contributions are as follows:

\begin{itemize}
\item We present \name,
  a \emph{coherent}, \emph{stable} and \emph{type-safe} formal model for
  implicit programming that supports local scoping, overlapping rules,
  first-class instances and higher-order rules.

%\item We identify the connection between the type-directed resolution
%  process of IP and focussing. The design of resolution in
%  our calculus is directly inspired by focused proof search, but
%  employs various additional techniques to ensure determinism.

\item We significantly improve the design of resolution over the
  existing work on the implicit calculus by Oliveira et al.~\shortcite{oliveira12implicit}. The new design for
  resolution is more powerful and expressive; it is closely based on
  principles of logic and the idea of propositions as types~\cite{propsastypes}; and is related 
  to the idea of focussing in proof search.  

\item \name comes with a semantics in the form of a type-directed elaboration
   to System~F. 

\item We provide a unification-based algorithm as an executable form
      of the declarative specification of resolution. A prototype implementation
      of this algorithm and of \name is available at \url{https://bitbucket.org/tom_schrijvers/cochis/}.

\item 
   We establish key meta-theoretic properties of our system:
   \begin{itemize}
   \item The elaboration is type-preserving.
   \item Resolution is deterministic and thus coherent.
   \item Resolution is stable under type substitution, as is elaboration under
         reduction of type application. 
   \item Our algorithm is sound and complete with respect to its declarative specification.
   \end{itemize}
   The proofs are available in the appendix and at \url{https://bitbucket.org/KlaraMar/cochiscoq} 
 
\end{itemize}


%-------------------------------------------------------------------------------
\paragraph{Organization} 
Section~\ref{sec:overview} presents an informal overview of our calculus. 
Section~\ref{sec:ourlang} describes a polymorphic type system that
statically excludes ill-behaved programs. Section~\ref{sec:trans} provides the elaboration 
semantics of our calculus into System F and correctness results. 
%Section 5 presents the source language and its encoding into $\ourlang$. 
Section~\ref{sec:related} discusses related work and Section~\ref{sec:conclusion} concludes.
\bruno{don't forget to revise organization after rewriting.}

%if False
This paper is a rewrite and expansion of the conference paper by Oliveira et
al. \shortcite{oliveira12implicit}.  It has one additional author
(Wadler), whose main contribution was to suggest a simplification to
the formulation of $\lambda_?$ in Section 3.  The previous work had
separate syntactic classes for types ($\tau$) and type rules ($\rho$),
and a complex construct $\forall \bar{\alpha}. \bar{\rho} \Rightarrow
\tau$ that abstracts over many types and rules at once; this paper
unifies types and rules into a single syntactic class ($\rho$) and has
separate constructs $\forall \alpha . \rho$ and $\rho_1 \Rightarrow
\rho_2$ that abstract over a single type or rule at a time.

The new formulation of  $\lambda_?$  also differs from the 
conference version in that resolution is generalized further and 
made more expressive. Section 3 presents a discussion about the 
differences in terms of expressivity. Furthermore, (also in Section 3)
we now include a treatment of termination and present an algorithm for 
resolution. Neither of these were discussed in the conference
version. Finally, our formalization is more detailed, having several
additional lemmas proving properties of the calculus; and we have 
significantly expanded our discussion of related work.
%endif


%%The companion technical report~\cite{oliveira12implicit} provides additional technical material
%%and proofs.
%%At the same time, it strives to be
%%a minimal core calculus consisting of only three constructs:
%%1) a query operator, 
%%2) a mechanism for assuming rules in scope, and 
%%3) another mechanism to supply evidence for assumptions.

% simple core calculus that essentially models a query
% language, resembling a simple logic programming language.  It consists of only
% four basic constructs: a query operator, a mechanism for introducing
% facts\tom{rules is a better word, facts in LP are rules without LHS} in scope,
% and another mechanism for binding evidence to facts and eliminating facts. 
% The rule calculus integrates all 4 features discussed by us and, consequently,
% provides a good foundation for studying the issues of scoping and resolution in
% IP mechanisms.

%Technical results

%%We present and compare two semantics for the implicit calculus: a type-directed
%%elaboration semantics and an operational semantics.  While the former is the
%%traditional approach, the latter is the first of its kind for implicit
%%programming: it enables a direct soundness proof and programs can be understood
%%independent of the type system. Moreover, because resolution happens at runtime,
%%a static type system for the operational semantics can accept more programs
%%than for the elaboration semantics, which performs all of resolution statically.

%%In the static type system, we pay particular attention to the different issues
%%that arise with \textit{overlapping rules}, especially with respect to coherence. 
%%Our setting of locally
%%scoped rules and the dynamic resolution in the operational semantic, allows us
%%to formulate alternative solutions for dealing with overlapping rules and
%%avoiding the associated pitfalls.


%%a situation where multiple rules
%%are eligible for resolving an implicit value. Such overlapping rules have shown
%%their use in Haskell and Scala, but
%%the semantic issues are essentially left unaddressed.  


% We present the type system, an operational semantics as well as 
% an elaboration semantics for the polymorphic rule calculus. The 
% operational semantics is proved sound with respect to the type 
% system, and we show that the elaboration semantics is type 
% preserving. Furthermore, both semantics are shown to have 
% the coherence property. Finally, we show that the operational semantics 
% proposed by us is a \emph{conservative extension} of the elaboration 
% semantics, allowing more programs to be accepted, while still preserving 
% coherence. 

% With respect to the operational semantics, it is worth remarking that
% it is the first operational semantics in the literature for an
% IP mechanism. Traditionally, the semantics or
% implementation of IP mechanisms has been through
% elaboration. The large majority of type-class related proposals, Scala
% implicits or proposals for \emph{concepts} in C++ is given a semantics
% in this way.  In this style of semantics there is a source language
% which is translated via a type-directed translation into a core
% language. As a result, soundness can only be proved indirectly, as a
% consequence of the type-preservation of the translation. A consequence 
% of the elaboration semantics is that it tightly couples the dynamic and
% static semantics and it is essentially not possible to understand the
% behavior of programs independently of the type system. Furthermore, 
% it leads to somewhat weaker metatheoretical results~\cite{}.

% Although our operational semantics requires type annotations in
% certain constructs to guide the dynamic execution of programs, 
% it is independent from the static semantics. The operational semantics 
% allows us to prove soundness in a direct style.  Furthermore, it
% offers an alternative to resolution, which is necessarily static 
% in the elaboration semantics. In contrast, our operational semantics 
% allows resolution to happen at run-time, which offers the possibility 
% to accept more programs. Indeed, as we shall see, the operational 
% semantics conservatively extends the elaboration semantics. 

%%We also sketch a simple, but realistic source language that translates to the
%%calculus in a type-directed manner. This source language relinquishes some
%%expressivity to suit type-inference. We discuss the remaining type inference
%%issues and relate them to the literature~\cite{outsidein}.
  


% With respect to related work, the most notable difference of the rule
% calculus is that it focuses on providing a core calculus that directly
% supports features related to IP. Most previous work,
% has typically studied each feature in isolation and has been built
% directly on source languages or core languages that have no built-in
% constructs for supporting IP. For example, with
% respect to local instances, \cite{} proposes an elegant design of type
% classes on top of ML-style modules, which allows instances to be
% selectively activated in a certain local scope. However, none of the
% other 3 features are addressed and the local instances proposed in
% that work cannot be nested (which avoids further issues with respect to
% overlapping instances). 

% \paragraph{Summary}
% The contributions of this paper are:
% \begin{itemize}
% 
% \item \textbf{The rule calculus:} A core calculus aimed at modeling 
% the scoping and resolution features of IP
% mechanisms. 
% 
% \item \textbf{Operational Semantics and dynamic resolution:}
% 
% \item \textbf{Source language and discussion about type-inference:}
% 
% \end{itemize}
% Instead type class interfaces are encoded using
% standard object-oriented interfaces and type class instances correspond to
% implicit objects that implement such interfaces. 

% In comparison to Scala --- which supports a form of local and
% overlapping instances, as well as type classes as types --- the key
% difference is that there is no formalism that models the Scala implicits
% mechanism in the literature. The design of the implicits mechanism is
% only informally described in the Scala reference \cite{}, and in a
% recent paper~\cite{}. More technically, the support for nested local 
% instances is ad-hoc and the current version of Scala does not ensure 
% coherent selection of instances. Furthermore, higher-order predicates 
% are not supported and support for type-inference in Scala is 
% very limited.  
% Notably, Haskell type
% classes assume that instances are globally visible and that there is only one
% possible instance for each type. Furthermore, type classes and types are
% considered distinct entities, the former being predicates (or relations) on the
% latter.

% In particular, the
% following topics have been discussed before in the literature:
% 
% %% * Limitations of type class mechanisms: 
% %%  higher-order predicates, local scoping, first-class type classes, 
% %%  any values can be implicit, overlapping instances. 
% 
% \paragraph{Local scoping} With Haskell type classes instances are
%   globally scoped, which essentially means that there can be only 
%   one instance per type in a program. While there are merits in the
%   choice of global scoping (for example with respect to principal
%   types \cite{}), for certain applications\bruno{mention references,
%     generic programming?} being restricted to a
%   single instance is too limiting and better control over scoping 
%   is desirable. As such, it is not a surprise that several alternative design 
%   proposals include some notion of local scoping
%   \cite{}. \bruno{Want to talk about Scala 
%   here but Scala should first be introduced, come back to this, or see
%   whet. Maybe I can talk about modular type classes later.} 
%    
% \paragraph {Overlapping instances and coherence} Related to scoping is the issue
%   of overlapping instances. Because selection of instances is
%   type-based, there are two important questions related to the
%   selection of instances. Firstly, what should happen if two instances of 
%   the same type are in scope? Secondly, in polymorphic systems like
%   Haskell, what should happen if two instances are in scope but one 
%   is more specific than the other? With global instances the standard 
%   answer to the first question is that programs with two instances of 
%   the same type should be rejected, whereas it is a much debated
%   question of what to do with respect to the second question. With
%   local instances the issue of overlapping instances is even more
%   subtle because for both questions it is debatable what the most 
%   appropriate thing to do is.   
% 
%   Ultimately, the issue of overlapping instances is one of the most
%   controversial in the design of IP
%   mechanisms. While certain implementations of Haskell offer some
%   support for overlapping instances, the semantic foundations of
%   overlapping instances are considered to be quite tricky and there is
%   very little work in that area. Notably a desirable property when
%   dealing with overlapping instances is \emph{coherence}.\bruno{Why 
%   is coherence desirable?}
%   Nevertheless, the experience with
%   Haskell libraries has shown that overlapping instances are useful in
%   practice.\bruno{Again, it may be worth mentioning Scala here,
%     because of the prioritized overlapping implicits, we may also 
%   want to point out that Scala implicits ignore the issue of coherence.}
% 
% \paragraph{Type classes as types} A primary characteristic in the 
% design of Haskell type classes is that regular types (such as
% integers, lists or records) and type classes are segregated. 
% Values of regular types are explicitly passed, and such types 
% can be abstracted through the use of polymorphism. However, 
% with type classes, the evidence (which corresponds to the values) 
% is implicitly passed and type classes cannot be abstracted. 
% While the Haskell design can be justified with the view that 
% type classes as predicates on types, the segregation between 
% type classes and regular types as been shown limiting for certain 
% applications. \bruno{Scala takes a different view}.  
% 
% \paragraph{Higher-order predicates} Finally, in Haskell, constraints 
% can only be first-order predicates. However, in practice the need 
% for higher-order predicates arises. For example, it is well-known
% that instances for datatypes involving parametrization on type constructors, 
% would benefit from higher-order predicates~\cite{}. Also some 
% sophisticated, yet widely used libraries such as the monad transformer 
% library (MTL), are limited in their design partly because of the lack 
% of higher-order predicates. As a result some ad-hoc tricks need to be 
% used to overcome such limitations\bruno{We probably need to
% substantiate this argument. Forward reference to an example in the paper?}. 
% 
% \subsection{The Rule Calculus}
%
% \bruno{What is resolution?}  The main contribution of this paper is
% the \textit{rule caculus}: a calculus aimed at the study of resolution and
% scoping issues that occur in IP mechanisms. From the
% four topics discussed above --- local scoping, overlapping instances,
% type classes as types, and higher-order predicates --- the first 2
% items are related to scoping, whereas the last 2 are related to
% resolution. While, every topic has been discussed before in the
% literature, there are no formalisms capable of providing all the
% features at once (or even some combinations) in the literature. 
% While every feature has shown its use in practice,
% it is not know whether all features can be integrated in a single, coherent
% system. 
% 
% The rule calculus is a simple core calculus that essentially models a query
% language, resembling a simple logic programming language.  It consists of only
% four basic constructs: a query operator, a mechanism for introducing
% facts\tom{rules is a better word, facts in LP are rules without LHS} in scope,
% and another mechanism for binding evidence to facts and eliminating facts. The
% rule calculus integrates all 4 features discussed by us and, consequently,
% provides a good foundation for studying the issues of scoping and resolution in
% IP mechanisms.
% 
% %Technical results
% 
% We present the type system, an operational semantics as well as 
% an elaboration semantics for the polymorphic rule calculus. The 
% operational semantics is proved sound with respect to the type 
% system, and we show that the elaboration semantics is type 
% preserving. Furthermore, both semantics are shown to have 
% the coherence property. Finally, we show that the operational semantics 
% proposed by us is a \emph{conservative extension} of the elaboration 
% semantics, allowing more programs to be accepted, while still preserving 
% coherence. 
% 
% With respect to the operational semantics, it is worth remarking that
% it is the first operational semantics in the literature for an
% IP mechanism. Traditionally, the semantics or
% implementation of IP mechanisms has been through
% elaboration. The large majority of type-class related proposals, Scala
% implicits or proposals for \emph{concepts} in C++ is given a semantics
% in this way.  In this style of semantics there is a source language
% which is translated via a type-directed translation into a core
% language. As a result, soundness can only be proved indirectly, as a
% consequence of the type-preservation of the translation. A consequence 
% of the elaboration semantics is that it tightly couples the dynamic and
% static semantics and it is essentially not possible to understand the
% behavior of programs independently of the type system. Furthermore, 
% it leads to somewhat weaker metatheoretical results~\cite{}.
% 
% Although our operational semantics requires type annotations in
% certain constructs to guide the dynamic execution of programs, 
% it is independent from the static semantics. The operational semantics 
% allows us to prove soundness in a direct style.  Furthermore, it
% offers an alternative to resolution, which is necessarily static 
% in the elaboration semantics. In contrast, our operational semantics 
% allows resolution to happen at run-time, which offers the possibility 
% to accept more programs. Indeed, as we shall see, the operational 
% semantics conservatively extends the elaboration semantics. 
% 
% To illustrate the usefulness of the rule calculus to model realistic
% source languages with IP constructs, we also 
% develop a simple Haskell-like source language which supports 
% the 4 features. This source language can be translated into the rule 
% calculus via a type-directed translation, which is shown to be 
% type-preserving. In the translation the various source language 
% constructs are modeled by combining the rule calculus constructs 
% with the standard constructs of the simply-typed lambda calculus. 
% The resulting language is less expressive than the rule calculus
% itself but, on the other hand, is amenable to type-inference. 
% A discussion about type-inference for this language, as well as
% several examples from the literature are presented.
%   
% With respect to related work, the most notable difference of the rule
% calculus is that it focuses on providing a core calculus that directly
% supports features related to IP. Most previous work,
% has typically studied each feature in isolation and has been built
% directly on source languages or core languages that have no built-in
% constructs for supporting IP. For example, with
% respect to local instances, \cite{} proposes an elegant design of type
% classes on top of ML-style modules, which allows instances to be
% selectively activated in a certain local scope. However, none of the
% other 3 features are addressed and the local instances proposed in
% that work cannot be nested (which avoids further issues with respect to
% overlapping instances). 




% It is not a surprise that alternatives have been proposed. 

%Why is Scala interesting

%%While Scala implicits are implemented and widely used, there is a lot
%%less research exploring the area of the design space covered by Scala.


%%However, important areas of the design space related to scoping and
%%resolution of type class instances remain relatively unexplored.

%%As pointed out by several researchers

%%As an attempt to provide a coherent framework in
%%which many type class extensions can be explained, \cite{} proposed
%%that if type classes are viewed as a particular use mode of ML-modules
%%then many extensions naturally follow for free.

%%Multiple
%%parameter type classes, functional dependencies, associated types 
%%fall in this category.   

%%As noted by several researchers, some of 

%%a lot of the focus of research about type class

%%has been on the ``type classes'' 
%%  (interfaces/ group of methods) part; less has been done on 
%%  scoping and resolution.

%% Following up on the observation that type classes and ML-modules
%% are closely related~\cite{}, \cite{} proposed a module system in which
%% modules can optionally be implicitly passed.

%%* Lots of work on type classes (and also qualified types)
%%  - However, a lot of the focus has been on the ``type classes'' 
%%  (interfaces/ group of methods) part; less has been done on 
%%  scoping and resolution.

%%* While Scala implicits are implemented and widely used, 
%%they have not been formalized.

%%Our solution

%%* The rule calculus. Just 3 constructs that deal with: 
%%  - scoping of implicits (local/lexical/nested scoping/overlapping instances)
%%  - resolution (higher-order predicates/any values of any type) 

%%* Any values of any Types can be implicitly passed (serve as evidence)

%%* Higher-order predicates 

%%* Local Scoping 

%%* First-class type classes

%%* Overlapping instances
%%  + incoherence

%%Operational Semantics

%% * Operational Semantics
%%  - Independent of the static semantics, although types are used to
%%  guide resolution. 

%% * Dynamic Resolution/Static Resolution
%% - coherence   


% \subsection{Old Stuff}
% 
% A recent trend in many programming languages is support for
% \emph{IP}.  \emph{IP} denotes a
% programming style where some values are automatically inferred by
% using available type information. IP is 
% useful because it allows implicitly passing many
% values that are tedious to explicitly pass it makes 
% the code more readable 
% 
% . because they simply follow 
% the type structure of another argument, or 
% 
% Haskell type classes~\cite{} are the
% most prominent example of IP. With type classes,
% \emph{type-class implementations} are inferred while performing
% type-inference. For example, in Haskell, the type of the |sort|
% function is as follows:
% 
% > sort :: Ord a => [a] -> [a]
% 
% In this case |Ord a| is a \emph{type-class constraint}. This
% constraint is used to ensure that implementations of comparison
% functions for values of type |a| exist. Such implementations, 
% called type-class instances, are defined by the user 
% 
% In its essence, the type class
% |Ord| is just an interface specifying a number of methods for
% comparing values of some type |a|. 
% 
% The |Ord| type class
% can be implemented for various types such as integers or lists of some
% type |a|. When the |sort| function is called the right implementation
% of |Ord| is selected by the compiler based on the instantiation of the
% type variable |a|. For example, calls like:
% 
% > sort [1,5,3]
% > sort [[1,5],[4,3]]
% 
% describes a particular programming style
% in which certain values used by a program can be \emph{inferred} by
% exploiting type-inference\footnote{This should probably be generalized
% to entail selection based on types, rather than just type-inference}.
% The most prominent example of a mechanism that supports implicit
% programming is given by Haskell type classes. With type classes,
% \emph{type-class dictionaries} (which are a specific kind of records) 
% are inferred while performing type-inference. A canonical
% example is given by a sorting function for lists in Haskell. The type
% of the |sort| function is as follows:
% 
% IP is to call functions without giving actual
% arguments.
% 
% % Haskell type classes have been widely used and proven to be one
% % effective programming feature. It is originated by the requirement of
% % supporting ad-hoc polymorphism in Hindley-Milner type system. It turns
% % out that we can simulate the things that are considered to only be
% % possible with dependent types with the recent extension of functional
% % dependencies or type families.
% 
% % The key ingredients of Haskell type class are two things: overloading
% % and resolution, whose combination is the essence of what we call {\it
% %   IP}. The use of overloaded entity raises {\it
% %   overloading constraints} which is reflected on the type of
% % expression. For the function with overloading constraints to be used
% % in the later call site, constraints should be {\it resolved} using
% % {\it resolution rules} registered by programmer.
% 
% % Inspired by Haskell type class, many systems with {\it implicit
% %   programming} feature have been proposed.
% 
% % The previous systems have explored the design space of overloading and
% % resolution. \cite{designspace} discusses many design considerations in
% % Haskell type classes. \cite{logic_over,theory_over} studied the
% % resolution. \cite{typeclasses_implicits} studied how Scala-style
% % overloading can support Haskell-style overloading. \cite{without}
% % studied type class-like system in untyped language, Scheme and
% % proposed predicate-based overloading scheme. \cite{modular} proposes
% % an interesting system which harmoniously embeds type class-like
% % feature into ML module system by adding additional usage mode of
% % modules.
% 
% % However, there has not been any work which proposes comprehensive
% % framework on IP. Many systems only supports global
% % scope of resolution rules. Most of them uses
% % static resolution.
% 
% % Especially, the previous systems suffers problem in modular
% % compilation when resolution rules can overlap each
% % other~\cite{designspace}.
% 
% % We propose a general system that is expressive enough to encompass
% % current practices and proposals and solves the intricacy incurred by
% % the overlapping.
% 
% \paragraph{Contributions} Our contributions are as follows.
% 
% \begin{itemize}
% \item We propose a core calculus $\lambda_{\rho}$ which supports the
%   following features of IP:
% 
%   \begin{itemize}
% 
%   \item Flexible implicit values: values of any types can be used as
%     implicit values. This is more general than Haskell type
%     classes~\cite{adhoc} and its extension to named
%     instances~\cite{named_instance, implicit_explicit} where only the
%     dictionaries can be passed implicitly.
% 
%     % Note that in
%     % Haskell type classes~\cite{adhoc} and its extension to named
%     % instances~\cite{named_instance, implicit_explicit}, only
%     % dictionaries can be passed to functions implicitly. This is
%     % generalized in ~\cite{modular} such that modules are used as
%     % implicit values, but this is still limited because modules are not
%     % first-class objects in their system.
% 
%   \item Lexical scoping: an implicit value has lexical scope where it
%     is used for resolution. Lexical scopes of implicit values can be
%     arbitrarily nested. Again, this is more general than the systems
%     with only global scope~\cite{adhoc, theory_over, snd_over,
%       logic_over}.
% 
%   \item Overlapping instances: two implicit instances can overlap each
%     other in the same implicit scope unless they make
%     ambiguity. Overlapping instances is regarded as a useful feature
%     but has not yet been handled properly~\cite{designspace}.
%     Especially, the combination of overlapping instances and lexical
%     scoping has not yet been discussed.
% 
%     % \item First-class instances: implicit instances can be freely
%     %   created, passed and registered to implicit scope at run
%     %   time. First-class instances are necessary for generic
%     %   programming~\cite{syb, sybclass}, so they have been partially
%     %   supported by Glasgow Haskell Compiler~\cite{ghc}. However, there
%     %   is no system that fully supports this.
% 
%     % \item High-order implicit constraints: as an additional benefit of
%     %   flexible implicit values, we can use types with higher-order
%     %   implicit constraints. 
% 
%   \end{itemize}
% 
%   These features have not yet been combined in any single system
%   proposed in the literature.
%   
% \item For our language, we provide two alternatives for resolving
%   implicit constraints; dynamic resolution, which always picks the
%   most specific instance for the given constraint but is not modular,
%   and static resolution, which is modular but fails to pick the most
%   specific one when there are overlapping instances. We explain in
%   detail about for which set of programs both resolution coincide and
%   for which they do not.
% 
% \item Based on our core calculus, we make a simple language that
%   supports all the features of core calculus with some restrictions
%   and still enjoys the benefits of type inference. There has been no
%   system that has all these features with type inference.
% 
% % \item High-order implicit constraints:
% 
% \end{itemize}

% \paragraph{Organization} Section \ref{sec:overview} is an overview of
% our calculus $\ourlang$ and shows how our calculus supports various
% features of IP using examples. Section
% \ref{sec:notation} defines notations to be used in the rest of this
% paper. Section \ref{sec:calculus} presents the formal system of
% $\ourlang$; operational semantics, polymorphic type system and
% type-directed translation are explained. Section \ref{sec:resolution}
% shows a detailed study on resolution in our system. Section
% \ref{sec:example} gives an example Haskell-like programming language
% as an instance of our general framework. Section \ref{sec:discussion}
% discusses some issues. Section \ref{sec:related} presents our
% exhaustive study on the previous work and comparison results. Section
% \ref{sec:conclusion} concludes.


%%% Local Variables: 
%%% mode: latex
%%% TeX-master: "../Main"
%%% End: 

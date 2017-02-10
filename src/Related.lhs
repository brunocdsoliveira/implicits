%include lhs2TeX.fmt
%include Scala.fmt
%include forall.fmt

\section{Related Work}
\label{sec:related}

This section discusses related work.

The goal of our work is to formalize a core language ($\ourlang$) with the
essential features of a type-directed implicit parameter passing mechanism equipped 
with recursive resolution. There have been several other proposals 
for core calculi which contain some form of implicit parameter passing 
and/or recursive resolution. However none of these allows for 
both implicit parameter passing for any types of values and
recursive resolution. Furthermore, although there have been some 
informal proposals for higher-order rules, the implicit calculus 
is the first system providing a full formalization of this feature.

%format model = "{\bf model}"
%format p2
%format p1

%-------------------------------------------------------------------------------
\subsection{Type Classes}

Several core calculi and refinements have
been proposed in the context of type-classes. As already discussed in
detail in Section~\ref{sec:intro}, there are a number of design choices that
(Haskell-style) type classes take that are different from the implicit
calculus. Most prominently, type classes make a strong differentiation
between types and type classes, and they use global scoping instead of
local scoping for the rule environment. These design choices can be
traced back to Wadler and Blott's~\shortcite{adhoc} original paper on type classes. In that
paper the authors argue that the inspiration for type classes came
from Standard ML's \emph{eqtype variables}. Eqtype variables 
were used to provide overloaded equality, by allowing type variables 
which range only over types that admit equality. Wadler and Blott
generalized that idea by allowing arbitrary predicates over types 
to be defined as type classes. This lead to type classes being viewed
as \emph{predicates over types} rather than types, and languages with 
types classes making a syntactic distinction between type classes and 
types. Implementations of type classes (that is, type class instances) 
are implicitly passed, whereas regular values implementing
types are explicitly passed. 

The reason for global scoping is also motivated by Wadler and Blott. They
wanted to extend Hindley-Milner
type-inference~\cite{hindley69principal,milner78theory,damas82principal} and
discovered that local instances resulted in the loss of principal types. In
both the implicit calculus and our source language there are sufficient type
annotations that the problem does not arise. However, the problem would indeed
arise in the source language if there were no top-level type annotations for a
program. For example, if we could write:

\vspace{5pt}

> implicit eqInt : Eq Int in
>   implicit eqChar : Eq Char in 
>     eq

\vspace{3pt}

\noindent (assuming the existence of values |eqInt| and |eqChar|) then,
without further annotations, the meaning of this program would be
ambiguous. In a language that strives for Hindley-Milner type-inference and principal types, 
this kind of ambiguity would be viewed as a serious problem. However, there 
are many languages with type-class like mechanisms (including Scala, 
Coq, Agda and Isabelle) that have more modest goals in terms of type-inference. 
In these languages there are usually enough type annotations that such 
ambiguity is avoided, and there is indeed added expressive power because 
type annotations drive the resolution process.

There are three possible behaviors here, which can all be accounted for
by our source language given a suitable type annotation for the program:

\begin{itemize}

\item With the type annotation | Int -> Int -> Bool| 
resolution picks the |eqInt| instance. 

\item With the type annotation | Char -> Char -> Bool| would pick |eqChar| instead.

\item With the type annotation |forall a. Eq a => a -> a -> Bool|, a third 
      implicit rule of type |Eq a| would have to be available in the implicit environment
      and resolution would pick that rule instead.
%%      \tom{Wouldn't there still be resolution that picks the implicit parameter?}

\end{itemize}

In other words, type annotations allow the user to control the resolution process according 
to the intended semantics.

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

\begin{comment}
An important difference between the implicit calculus and Haskell 
type classes is on how matching of type class instances work. 
The implicit calculus approach is quite \emph{eager} in that when 
looking up the implicit environment, the first instance that unifies 
is selected (see the ``triangle'' relation). Haskell's approach 
to selection is lazier.

> instance T  
\end{comment}

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


\subsection{Local Scoping}

\emph{Implicit parameters}~\cite{implicit_param} are a proposal for a
name-based implicit parameter passing mechanism with local scoping. Lewis et al.
formalized a small core language with the mechanism and there is also
a GHC Haskell implementation. Implicit parameters allow \emph{named}
arguments to be passed implicitly, and these arguments can be of any
type. Using
implicit parameters\footnote{Here we use the implementation available
  in the GHC Haskell compiler. The reader should note that the
syntax used in GHC differs from the syntax used in the original
paper~\cite{implicit_param}.} we could for example, write the following program:

%format eqD1 = "\Varid{?eqD}"
%format p1

\vspace{5pt}

> data EqD a = EqD {eq' :: a -> a -> Bool}
>
> eq :: (?eqD :: EqD a) => a -> a -> Bool
> eq = eq' (?eqD)
>
> eqInt    :: EqD Int                           -- Definition omitted 
> eqMaybe  :: (?eqD :: EqD a) => EqD (Maybe a)  --Definition omitted
>
> p1 = let eqD1 = eqInt in eq 3 4

\vspace{3pt}

Here the intention is to model something similar to Haskell's |Eq|
type class or the code in Figure~\ref{fig:eq}. The definitions |eqInt| and
|eqMaybe| play the role of the rules. The implicit parameters
are named, so that later they can be resolved from a local scope that
binds named arguments. This resolution process is illustrated in
program |p1|: the |eqInt| dictionary is brought into the local scope
(bound to the variable |eqD|) and used in the expression |eq 3
4|. In this case, the use of implicit parameters does not look too 
different from the implicit calculus.  
However, implicit parameters do not support recursive resolution,
so for most use-cases of type-classes they require composing 
rules manually, instead of relying on the recursive resolution 
mechanism to do this automatically. For example, the program:

\vspace{5pt}

> p2 =  let eqD1 = (let eqD1 = (let eqD1 = eqInt in eqMaybe) in eqMaybe) 
>       in eq (Just (Just 3)) (Just (Just 4))

\vspace{3pt}

\noindent illustrates a situation where we would like to compare  two
expressions |(Just (Just 3))| and |(Just (Just 4))|. This can be done 
by using the rule |eqMaybe| twice and using the rule |eqInt| once.
While in the implicit calculus recursive resolution would
automatically compose these rules, with implicit parameters 
the rules have to be manually composed.  

\paragraph{System $F^{G}$} System $F^{G}$~\cite{systemfg} also offers an implicit 
parameter passing mechanism with local scoping, which is used
for concept-based generic programming. 
Instead of a name-based approach, a type-directed approach is used
for passing implicit parameters. This is closer to the implicit calculus.
Program |p1| could be modelled as follows in System $F^{G}$:

\vspace{5pt}

%{

%format dots = "\ldots"
%format concept = "\bf{concept}"
%format model = "\bf{model}"
%format fn = "\bf{fn}"
%format < = "\langle"
%format > = "\rangle"

> concept Eq<t> {
>   eq : fn(t,t) -> Bool;
> } in 
>
> let p1 = model Eq<int> {dots} in eq[int] 3 4

%}

\vspace{3pt}

\noindent The |concept| declaration provides the interface for |Eq<t>|
concepts, whereas the |model| declaration provides the corresponding 
implementation of the concept. A difference to the implicit
calculus is that declaring a model automatically adds that model to the implicit
environment. In program |p1| we must both provide the model and add 
it to the implicit environment in a single step. In the implicit
calculus, these two aspects are decoupled.
A more important difference to the implicit calculus is that, like type classes, there is a
strong differentiation between types and concepts
in System $F^{G}$:
concepts cannot be used as types; and types cannot be used as
concepts. As a consequence, models implementing concepts can only 
be passed as implicit parameters, and regular values can only be
passed as explicit parameters. 

In contrast to $\ourlang$, System $F^{G}$ has both a notion of concepts
and implicit instantiation of concepts\footnote{Note
  that instantiation of type variables is still explicit.} built-in. 
This has the advantage that language designers can just reuse
that infrastructure, instead of having to implement it (as we did in Section~\ref{sec:example}). The language 
G~\cite{G} is based on System $F^{G}$ and it makes good use of these built-in mechanisms. However, 
System $F^{G}$ also imposes important design choices, such 
the use of a notion of concepts that is built-in to
the calculus. In contrast $\ourlang$ offers a freedom of choice (see
also the discussion in Section~\ref{subsec:extensions}). 

 
Finally System $F^{G}$ only formalizes a very simple
type of resolution, which does not support recursive resolution. 
To create program |p2| a model:

\vspace{5pt}

> model Eq<Maybe[Maybe[Int]]> {dots}

\vspace{3pt}

\noindent that manually composes rules must first be created in System
$F^{G}$. 

\textit{Modular type classes}~\cite{modular} are a language design
that uses ML-modules to model type classes.  The main novelty of this
design is that, in addition to explicit instantiation of modules,
implicit instantiation is also supported. In this design local scoping is
allowed. However, unlike $\ourlang$ (and also System
$F^{G}$ and implicit parameters) the local scopes cannot be nested.
Furthermore, implicit instantiation is limited to modules (that is 
other regular values cannot be implicitly passed and automatically resolved).

\subsection{Scala Implicits}

The main inspiration for our work comes from Scala implicits~\cite{implicits,scala}. Like our 
work Scala implicits allow implicit parameters of any types of values
and recursive resolution is supported. Prior to our work,
there was no small core calculus or any other form of formalization
for this style of implicit parameters. The main objective of our work 
was the formalize the essence of the ideas behind Scala implicits.
What we promote on this work is that the key idea of implicits is
a type-directed implicit parameter passing mechanism that works 
for all types of values and supports local scoping with recursive resolution.
However, we should note that our goal is not to have a faithful 
formalization of Scala implicits, since many other orthogonal aspects 
of the mechanism are tailored for the particularities of the Scala language.

%format v1 = "\Varid{v_1}"
%format v2 = "\Varid{v_2}"

%{

%format . = "."

%\begin{figure}
%\small
\begin{code}
   trait A {
     implicit def id[a] : a => a = x => x

     def ?[a](implicit x: a) = x
  }

  object B extends A {
     implicit def succ : Int => Int = x => x + 1

     val v1 = (?[Int => Int]).apply(3)          // evaluates to 4
     val v2 = (?[Char => Char]).apply('a')  // evaluates to 'a'
  }
\end{code}
%\caption{Nested Scoping with Overlapping Rules in Scala}

%\label{fig:scala}

%\end{figure} 

%}

Therefore there are noteworthy differences between $\ourlang$ and
Scala implicits. In contrast to $\ourlang$, Scala has subtyping. We do
not think that subtyping is essential, and it complicates the
formalization: as discussed in Section~\ref{subsec:extensions}
subtyping would require considerable adaptations to our calculus.
Therefore we have omitted subtyping here.  Although Scala also
provides local and nested scoping, nested scoping can only happen
through subclassing and the rules for resolution in the presence of
overlapping instances are quite ad-hoc. Figure~\ref{fig:scala}
illustrates the idea of nested scoping in Scala. Note that Scala
implicits do not natively support the query expressions (|?|), but we
can easily encode this functionality.  In Scala each trait/class
declaration introduces a scope and trait/class extension allows
extending that scope. Thus in trait |A| an implicit rule for type
|forall a. a -> a| is introduced.  In object |B| the scope of |A| is
extended and a new, overlapping, rule (|succ|) of type |Int ->
Int| is added\footnote{Note that introducing this rule directly in |A| would
  result in an ambiguity problem, since two overlapping rules are not
  allowed within the same trait/class.}.  Like the implicit calculus
the later rule takes priority when a query of type |Int -> Int| is
required. However, in Scala the rules of scoping are more complicated
than in the implicit calculus.  If more than one implicit value has
the right type, there must be a single “most specific” one according
to an ordering.  Informally this ordering states that a rule A is more
specific than a rule B if the relative weight of A over B is greater
than the relative weight of B over A. The relative weight is a score
between 0 and 2, where A gets a point over B for being as specific as
B, and another if it is defined in a class (or in its companion
object) which is derived from the class that defines B, or whose
companion object defines B. Roughly, a method is as specific as a
member that is applicable to the same arguments, a polymorphic method
is compared to another member after stripping its type parameters, and
a non-method member is as specific as a method that takes arguments or
type parameters. In other words Scala's scoring system attempts to account 
for both nested scoping through subclassing and the most specific type, whereas in the 
implicit calculus only the lexical scope is considered.
Finally, Scala has no (first-class) rule abstractions and
consequently no support for higher-order rules. Rather,
implicit arguments can only be used in definitions. 

\subsection{Type Classes, Theorem Proving and Dependent Types}

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

\begin{comment}
\emph{Canonical structures} were added to the Coq theorem
prover in \ldots. The implementation of this mechanism is tightly
coupled with Coq's type-inference mechanism,
\end{comment}

\subsection{Other Related Work} 

%if False

We first summarize how our work is in general different from existing
work and then make a more detailed comparison with
respect to scoping, overlapping, coherence, semantics and resolution. 
%
%% \subsection{Scoping and Resolution}

Our work distinguishes itself from previous work in several respects. 
We capture key features of 
IP in a minimal core calculus $\ourlang$. The calculus
shows a seamless integration of a number of
IP features --- local and nested scoping;
higher-order rules and queries; and overlapping rules --- that have
only been studied in isolation before. Furthermore, the calculus'
minimalistic and core nature makes it an ideal platform for a study of
key issues in IP such as scoping and resolution. In contrast,
most existing IP mechanisms have been implemented or
studied as part of a larger source language, hence some artificial restrictions
are imposed by the intricacies of the source language, which makes the
study of issues such as scoping and resolution hard. 
Finally, thanks to the calculus we can understand and address the
problem of ensuring coherence in the presence of overlapping rules and
nested scoping. 

%endif

%%\subsection{Design choices}
%%The design space of implicit programming mechanisms is quite big.
%%Various implicit programming mechanisms considerably differ in their
%%design. 

%if False

%format v1 = "\Varid{v_1}"
%format v2 = "\Varid{v_2}"

\begin{figure}
\begin{code}
   trait A {
     implicit def id[a] : a => a = x => x

     def ?[a](implicit x: a) = x
  }

  object B extends A {
     implicit def succ : Int => Int = x => x + 1

     def func[a](x : a) = (?[a => a]).apply(x)

     val v1 = func[Int](3)  // evaluates to 3
     val v2 = (?[Int => Int]).apply(3) // evaluates to 4
  }
\end{code}
\caption{Nested Scoping with Overlapping Rules in Scala}

\label{fig:scala}

\end{figure}

\paragraph{Closest Designs}

Closest to our design is that of Scala
implicits~\cite{implicits,scala}. Like implicits, $\ourlang$ provides
a simple mechanism for defining functions with implicit arguments;
resolution works with types directly and, consequently, no separate
notion of ``type class'' is required. Furthermore, Scala also has local
and nesting scoping. 

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

Another design that is closely related to ours is a recent proposal
for \emph{instance arguments} in Agda~\cite{instanceargs}. 
%This proposal is
%significantly inspired by the design of Scala implicits, but the 
Its most distinctive feature in comparison with Scala is that it supports
{first-class} implicit functions. In Scala it is not
possible to pass a function with implicit parameters to another
function. Rules in $\ourlang$ can  also  be
first-class implicit functions, but unlike instance arguments we 
can express higher-order rules.  Moreover, rules take
{sets} of arguments rather than single (instance) arguments.
As we have seen in Section~\ref{sec:example}, the use of sets makes it easy
to build source languages that infer sets of constraints (like Haskell).
Unlike most IP mechanisms, instance
arguments do not allow explicit selection of rules for resolution and 
resolution is limited in its expressive power, to avoid introducing 
a different computational model in Agda. Finally, the issue of
coherence in the presence of overlapping rules is not discussed.



\paragraph{Scoping, Overlapping, and Coherence}
%Several works have discussed scoping mechanisms for IP. 
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

The GHC Haskell compiler supports overlapping instances~\cite{designspace},
that live in the same global scope. Our calculus generalizes this idea to
local scoping. The problem with GHC's scope is that deciding coherence requires
global information. This is at odds with modular compilation. As GHC prefers
the latter, it does not 
guarantee coherence across modules.

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



\paragraph{Semantics}

Our calculus' dynamic semantics is defined as a big-step operational
semantics. This contrasts with the majority of IP mechanisms.  Most IP
mechanisms have a semantics based on translation, in which the queries
are resolved statically. Several researchers~\cite{tchaskell,snd_over}
have pointed out weaknesses to such translation semantics: the static
and dynamic semantics cannot be understood independently, and there is
no semantic soundness result. Thatte's work~\cite{semantics_typeclass}
is one interesting exception where we have a translation semantics,
but resolution happens dynamically. Essentially a program with type
classes is translated into an ML-like calculus with typecase, which is
used to handle the type-based dispatching of type classes. Still this
work suffers from not having a direct soundness result with respect to
the dynamic semantics.

There are a few other works that provide a dynamic semantics for IP,
but they have some restrictions that our calculus' operational
semantics does not. Notably the works by Odersky et
al. \shortcite{snd_over} and Kaes \shortcite{kaes} both provide
a translation and denotational semantics for their overloading
mechanisms. % As as far as we know, $\ourlang$ is
% the third system provides dynamic semantics as a foundation for type
% system and translation. 
% Kaes's work \cite{kaes} is one of the earliest work in the type class
% field. 
However, Kaes's system does not 
support overlapping, local scoping and polymorphic instances. 
Odersky et al.'s system, cannot make instances that are polymorphic
in the return type. Besides, their dynamic semantics require runtime
type checking to resolve overloaded instances. Our operational semantics, on
the contrary, has none of these restrictions and does not need to
check the type of a value at runtime. 

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Resolution}
Resolution in $\ourlang$ is significantly more expressive than in
other systems. Notably resolution supports higher-order rule types and
queries, as well as queries for polymorphic types. A closely related
design sketch is that of higher-order predicates by Hinze and Peyton
Jones~\shortcite{derivable}. However, similar extensions have not been
adopted by any other IP systems.

As such, the interaction with other features is first studied by our work.
Hinze and Peyton Jones only list a system of inference rules, but do not study
any of its properties. Notably, they propose the more expressive
resolution rule discussed in Section~\ref{subsec:opsem}, but do not consider
its impact on coherence in the presence of overlap (nor on termination)
that motivates the simplification in our design.


As Hinze and Peyton Jones show, higher-order predicates are specially important
when dealing with types that involve type constructor polymorphism. In order to
simplify presentation, our formalization of the implicit calculus does not
include type constructor polymorphism. However, such an extension is
straightforward. %%, as our implementation shows.

\paragraph{``Type class'' interfaces}
$\ourlang$ focuses on scoping and resolution, which contrasts with a
lot of recent work on IP mechanisms, where the focus
has been on increasingly more powerful ``type class'' interfaces. For
instance, \emph{functional dependencies}~\cite{fundeps},
\emph{associated types}~\cite{assoctypes,assoctypes2} and \emph{type
  families}~\cite{typefunc} are all examples of this trend. This line
of work is orthogonal to ours. In essence, although $\ourlang$ does
not provide a special type of ``type class'' interface natively, this
does not preclude the definition of source languages which have such
interfaces. The idea is that such interfaces can be added as
extensions, very much in the same way that we added records in our
source language in Section~\ref{sec:example}. The design of Scala implicits,
modular type classes and instance arguments~\cite{instanceargs} in Agda shows that,
when a good notion of interface exists in the base language, the
addition of an IP mechanism makes many advanced
features such as associated types fall out essentially for free.

%endif

\paragraph{Resolution with Higher-order Rules} 
Resolution in $\ourlang$ is significantly more expressive than in
other systems. Notably resolution supports higher-order rule types and
queries, as well as queries for polymorphic types. A closely related
design sketch is that of higher-order predicates by Hinze and Peyton
Jones~\shortcite{derivable}; no other IP system has adopted a similar extension.

As Hinze and Peyton Jones show, higher-order predicates are specially important
when dealing with types that involve type constructor polymorphism. In order to
simplify presentation, our formalization of the implicit calculus does not
include type constructor polymorphism. 

Our work is the first to study the meta-theory of higher-order rules as part of
a language. Hinze and Peyton Jones only list a system of inference rules, but
do not study any of its properties.

\paragraph{Type Classes and Logic Programming}
The connection between Haskell type classes and Prolog is folklore. 
Neubauer et. al.~\shortcite{Neubauer} also explore the connection with \textit{Functional Logic Programming}
and consider different evaluation strategies to deal with overlapping rules.
With \emph{Constraint Handling Rules}, Stuckey and Sulzmann~\shortcite{theory_over} use \textit{Constraint Logic Programming}
to implement type classes.

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

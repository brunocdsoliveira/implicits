%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Rule.fmt

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

Implicit programming infers values by using type information. It is
``implicit'' because we can omit expressions (e.g. those for function's
parameters) and instead implicitly rely on its type-directed inference
of necessary values. 
%mentioning a type does not explicitly pinpoint a
%value by an expression but just means a value of that type.
Implicit values are either fetched by their types from
the current (implicit) environment or constructed by type-directed \emph{rules}. 

Implicit programming has proven its benefits in practice.  Haskell's
\emph{type classes}, Scala's \emph{implicits} , JavaGI, various
proposals for C++'s \emph{concepts} are all implicit programming
mechanisms. Implicit programming significantly reduces the amount of tedious,
explicitly passed expressions, it can be used to model a {constrained
  polymorphism}, and it offers a powerful and disciplined form of
{overloading}.

As a small, but realistic use-case of implicit programming consider a
\emph{polymorphic} sorting function.

< sort : forall a . {a -> a -> Bool} => List a -> List a

Implicit programming offers a convinient way to define such a
function. Sorting cannot be defined as a purely parametric polymorphic
of type |forall a. List a -> List a|, because it needs to know how to
compare the elements of the list. However \emph{explicitly} passing a
comparison function, can be very tedious: it is likely that for a
given type the sorting function is called with the same comparison
function over and over again. By using an implicit argument for 
passing the comparison function around this problem can be elimated. 

Consider the following program:

< implicit {cmpInt : Int -> Int -> Bool} in
<   (sort [2,1,3], sort [5,9,3])

The important thing to note is that in this program the two calls of
the sorting function take only one argument: the list to be sorted.
The comparison function used by the sorting function (|cmpInt|) is
\emph{implicitly} passed. It is retrieved automatically from the 
implicit environment in a process called \emph{resolution}. 
In this example, the implicit environment is 
built using the |implicit| construct, which is a \emph{scoping}
construct that brings |cmpInt| into the scope of the 
expression | (sort [2,1,3], sort [5,9,3]) |.

Scoping and resolution are two essential features of implicit 
programming mechanisms. However, because often implicit 
programming mechanisms are studied in the context of larger 
source language, scoping and resolution do not get the appropriate 
attention and are somehow (artificially) restricted to suit with 
the particular source language.

This paper presents $\ourlang$: a powerful and expressive, yet
minimalistic, calculus for studying the \emph{scoping} and
\emph{resolution} of implicit programming mechanisms.

In the following we will first introduce $\ourlang$ and how its
constructs are useful to model desired functionality in general
implicit programming mechanisms. Then we will expose problems of
existing implicit programming practice with respect to scoping and
resolution, and then summarize our contribution.

\subsection{Modelling Implicit Programming in $\ourlang$}
%% We first introduce, in a general manner, implicit programming by
%% enumerating its essence without being constrained by existing
%% practice. For this purpose we will use our calculus notation. For the
%% readers who are familiar with implicit programming practice, we will
%% sometimes add corresponding examples in notation reminescent of the
%% practice.

%% We then expose problems of existing implicit programming practice 
%% from this general point of view toward implicit programming, and we 
%% summarize our contribution. 

%%\begin{itemize}

%%\item {Implicit programming} fetches values by types and uses types to
%%  infer values. For example the definition of an addition function
%%  that adds one implicit value to an explicit one would be:

%%\begin{verbatim}
%%add : Int => Int -> Int
%%add x = ?Int + x
%%\end{verbatim}

%%To fetch the value of the implicit argument, we use a \emph{query}
%%``$\qask{\tyInt}$''. This query looks up the implicit enviroment for
%%a value associated to the type $Int$.   

%% function $add$ 

\paragraph{Fetching values by types:} $\ourlang$ fetches values by types, not by names.
  For example, the argument for an increment function's can be
  looked up from the implicit environment as follows:
\[
\texttt{inc}\; (\qask{\tyInt}).
\]
The \emph{query} ``$\qask{\tyInt}$'' uses the current implicit
environment to fetch a value of type \tyInt. 

%%Function \texttt{inc} is applied to an argument (we call ``implicit
%%query'') that queries ``$\qask{\tyInt}$'' by mentioning just its
%%type \tyInt.  The int-typed entry in the current implicit
%%environment is looked up  to provide an integer value. 

%%In practice, the implicit query ``$\qask{\tyInt}$'' can even be
%%omitted thanks to type inference. Our calculus makes implicit queries
%%always manifest in text. 

\paragraph{Type-directed rules:} $\ourlang$ constructs values, using
  programmer-defined, type-directed value-resolution rules  (
  similar to functions). Value-resolution rules (rule abstractions) define how
  to compute, from implicit arguments, the values of an intended
  type. For example, a rule that computes a pair of int and bool from
  implicit int and bool values would be:
\[
\qlam{\tyInt, \tyBool}
     {\texttt{(\qask{\tyInt}+1, not\;\qask{\tyBool})}}.
\]
We write the above rule's type as
$\rulety{\tyInt,\tyBool}{\tyInt\times\tyBool}$. 

Hence, where a value of $\tyInt\times\tyBool$ is needed (expressed by 
a query $\qask{(\tyInt\times\tyBool)}$), 
the above rule can be used if int and bool
values are available in the current implicit environment. Under such
environment, the rule returns a pair of the int and bool values after 
respectively incrementing and negating those values. 

Implicit environments are built by rule applications
(analogous to building environments using function applications).
In our notation, rule application is expressed as, for example:
\[
\qapp{\qlam{\tyInt, \tyBool}
      {\texttt{(\qask{\tyInt}+1, not\;\qask{\tyBool})}}
     }{\{\texttt{1},\texttt{true}\}}.
\]
Using a syntactic sugar, which is analogous to the \texttt{let}-expression, the
above application is expressed as:
\[
\qlet{\{\texttt{1},\texttt{true}\}}
     {\texttt{(\qask{\tyInt}+1, not\;\qask{\tyBool})}}
\]
which returns $(2,\Meta{false})$. 

\paragraph{Higher-order rules:} $\ourlang$ supports higher-order
rules. For example, a rule
\[
\qlam{\tyInt,\rulety{\tyInt}{\tyInt\times\tyInt}}{\qask{(\tyInt\times\tyInt)}}
\]
of type
$\rulety{\tyInt,\rulety{\tyInt}{\tyInt\times\tyInt}}{\tyInt\times\tyInt}$ 
computes an integer pair given an integer and a rule to
compute an integer pair from an integer.

Hence, the following example will return $(3, 4)$:
\[
\qlet{\{\texttt{3},\qlam{\tyInt}{\texttt{(\qask{\tyInt},\qask{\tyInt}+1)}}\}}
     {\qask{(\tyInt\times\tyInt)}}.
\]
Resolving (computing a value for) the implicit query
$\qask{(\tyInt\times\tyInt)}$ follows 
a simple inference: the goal is to have a pair of integers, yet the current
environment has no such pair but has an integer $3$ and a rule 
$\qlam{\tyInt}{\texttt{(\qask{\tyInt},\qask{\tyInt}+1)}}$
to compute a pair from an integer. Hence we can apply the pair
construction rule to $3$ to construct the $(3,4)$ pair for the implicit query. 

\paragraph{Polymorphic rules:} $\ourlang$ allows polymorphic rules. For example, rule 
\[
\qLam{\alpha}{\qlam{\alpha}{(\qask{\alpha},\qask{\alpha})}},
\]
whose type is $\forall\alpha.\rulety{\alpha}{\alpha\times\alpha}$, can be
instantiated to multiple rules of monomorphic types
\[
\rulety{\tyInt}{\tyInt\times\tyInt}, 
\rulety{\tyBool}{\tyBool\times\tyBool}, \cdots.
\]
Hence multiple monomorphic queries can be resolved by the same
rule. For example, the following expression returns
$((3,3),(\Meta{true},\Meta{true}))$: 
\[
\begin{array}{l}
\texttt{implicit}\\
\mbox{\ \ \ \ }\{\texttt{3},\;\texttt{true},\;
      \qLam{\alpha}{\qlam{\alpha}{(\qask{\alpha},\qask{\alpha})}}\}\\
\texttt{in}\\
\mbox{\ \ \ \ }
\texttt{(\qask{(\tyInt\times\tyInt)},\qask{(\tyBool\times\tyBool)})}.
\end{array}
\]

\paragraph{Combining higher-order and polymorphic rules:} 
For example, the following rule 
\[
\qlam{\tyInt,\forall\alpha.\rulety{\alpha}{\alpha\times\alpha}}
 {\qask{((\tyInt\times\tyInt)\times(\tyInt\times\tyInt))}}
\]
prescribes how to build a pair of integer pairs, inductively from an
integer value. Begining from an integer value, consecutively applying the 
argument rule of type
\[
\forall\alpha.\rulety{\alpha}{\alpha\times\alpha}
\]
twice: first to an integer, then to its result (an
integer pair) again.

That is, the following expressiong returns $((3,3),(3,3))$:
\[
\begin{array}{l}
\texttt{implicit}\\
\mbox{\ \ \ \ }\{\texttt{3},\;
      \qLam{\alpha}{\qlam{\alpha}{(\qask{\alpha},\qask{\alpha})}}\}\\
\texttt{in}\\
\mbox{\ \ \ \ }
\texttt{\qask{((\tyInt\times\tyInt)\times(\tyInt\times\tyInt))}}.
\end{array}
\]
The $(3,3)$ pair is from applying the rule 
$\qLam{\alpha}{\qlam{\alpha}{(\qask{\alpha},\qask{\alpha})}}$
to $3$, and the final answer $((3,3),(3,3))$ from applying the same
rule to $(3,3)$.

\paragraph{Locally and lexically scoped rules:} Suppose the rule 
\[
\qlam{\tyInt}
 {\qlam{\tyBool, \rulety{\tyBool}{\tyInt}}
       {\qask{\tyInt}}
 }
\]
is applied to an integer and then to a boolean and a rule
of type $\rulety{\tyBool}{\tyInt}$. Resolving the implicit query
$\qask{\tyInt}$ always selects the lexically nearest possible
resolution.

That is, resolution of the implicit query $\qask{\tyInt}$ is not from
fetching the integer value but from applying to the boolean value the
rule that returns an integer from a boolean. Following example thus
returns $2$ not $1$:
\[
\begin{array}{l}
\texttt{implicit}\;\{\texttt{1}\}\;\texttt{in}\\
\mbox{\ \ \ }\texttt{implicit}\;\{\texttt{true},\;
\qlam{\tyBool}{\texttt{if}\;\qask{\tyBool}\;\texttt{then 2}}\}\;\texttt{in}\\
\mbox{\ \ \ \ \ \ }\qask{\tyInt}.
\end{array}
\]

\paragraph{Overlapping rules and coherency:} Two rules overlap if their
  return types intersects, hence they can both be used 
  to resolve the same implicit query. 

  The coherency principle states
  under what conditions the behavior of resolution is consistently
  predictable in the presence of overlapping rules. 
  Without coherency, programming with implicit values is a tricky
  business, fragile and unpredictable. 

  The conherency: the most concrete resolution rule is
  always chosen modulo the lexical scoping. For example, consider the
  following code: 
\[
\begin{array}{l}
\texttt{let}\;\texttt{f}:\forall\beta.\beta\to\beta = \\
\mbox{\ \ \ }\texttt{implicit}\;
  \{\lambda x.x:\forall\alpha.\alpha\to\alpha\}\;\texttt{in}\\
\mbox{\ \ \ \ \ \ }\texttt{implicit}\;
   \{\lambda n.n+1:\tyInt\to\tyInt\}\;\texttt{in}\\
\mbox{\ \ \ \ \ \ \ \ \ }\qask{(\beta\to\beta)}\\
\texttt{in}
\mbox{\ \ \ }\texttt{f} [\tyInt] \texttt{1}\;\cdots\;
             \texttt{f} [\tyBool] \texttt{true}.
\end{array}
\]
The definition of \texttt{f} uses two nested scopes to introduce two
overlapping values in the implicit environment.
According to the consistency principle, resolving the 
implicit query $\qask{\beta\to\beta}$ is determined at \texttt{f}'s
instantiations: the first $f$ must be $\lambda
n.n+1$ and the second $f$ must be $\lambda x.x$. 
%% \end{itemize}

%This \emph{resolution} mechanism to automatically infer
%function arguments based on available type information.  User-supplied
%\emph{rules} determine which values resolution infers. 

\subsection{Problem}
Current implicit programming practice (e.g. Haskell's type classes,
Scala's implicits, C++'s concepts) fails to support 
the above implicit programming features in full combination.

\paragraph{Type classes}
Haskell {type classes}~\cite{adhoc}, which is the
most prominent implicit programming mechanism, explore
only a particular corner of the large design space of implicit
programming~\cite{designspace}, and they have 3 notable limitations:

\begin{itemize}

\item Haskell's resolution rules are global. Hence, there can only be a
single rule for any given
type~\cite{named_instance,overloadingCamarao,implicit_explicit,modular}. No local scoping of rules are available. 
This is an noticeable limitation that already received several proposals for its
fix: rules can be named~\cite{named_instance} or locally
scoped~\cite{overloadingCamarao,implicit_explicit,modular}.
% Kahl and Scheczyk~\cite{named_instance} proposed to address this
%problem with \emph{named instances}, offering the possibility to name
%instances and manually select instances for resolution using these
%names. Others have suggested mechanisms that allowed
%\emph{local scoping} of
%instances~\cite{overloadingCamarao,implicit_explicit,modular}, thus
%offering control over which instances are on scope rather than having
%a single global scope. 
%

\item Haskell type classes are, in some sense, a second class construct
compared to regular types: it is not possible to abstract over a type 
class in Haskell~\cite{restricted}. Yet, the need for first-class type
classes is real in practice~\cite{sybclass, scalageneric}.

\item Finally type classes do not support higher-order rules. As noted by 
Hinze and Peyton Jones~\cite{derivable}, certain Haskell datatypes
like:

> data Perfect f a = Nil | Cons a (Perfect f (f a))

(a variation of the well-known perfect tree type)
require type class instances such as:

> instance (forall b. Show b => Show (f b), Show a) => 
>   Show (GPerfect f a)

which are not possible to define in Haskell, since Haskell is
restricted to first-order instances (or rules).  This rule is
higher-order because it assumes another rule, |forall b. Show b =>
Show (f b)|, that itself contains an assumption. Note also that this
assumed rule is polymorphic in |b|.  In contrast, as we have seen, in $\ourlang$ such
higher-order rules are allowed:
 
< forall f a . {forall b. {Show b} => Show (f b), Show a} 
<               =>  Show (GPerfect f a)

\end{itemize}

%Finally, type class
%constraints consist, essentially, of first-order rules, %predicates on types,
%but for some applications \emph{higher-order rules} are %predicates} are
%needed~\cite{derivable,scalageneric}.

\paragraph{Scala implicits} The Scala implicits~\cite{implicits}
mechanism provides an interesting alternative implicit programming
design. Unlike type classes it provides locally scoped rules. Moreover
any types can be used as implicit parameters and there's no special 
separate type-class-like interface. Because such interfaces are
modelled with regular types, they can be abstracted over and do 
not suffer from the second class nature of type classes. 

However, implicits only informally described~\cite{implicits,scala}
and some of the design decisions are quite ad-hoc. In particular, 
although Scala allows \emph{nested} local scoping and overlapping rules
\textit{coherence} is not guaranteed, making the use of overlapping
rules quite impredictable. Moreover, Scala does not support
higher-order rules.  

%%The consistency is broken. For the above consistency example, Scala
%%assigns $\lambda x.x$ to both calls to $f$, though $\lambda n.n+1$ is
%%more concrete evidence for $f\;1$.

%differs from Haskell
%type classes in several ways and has its own limitations too.
%In Scala, any value can be made implicit: Scala does not
%segregate type classes and types like Haskell and, as a consequence it
%is possible to abstract over the types representing type
%classes. 
%Secondly, implicit values (which roughly correspond to type
%class instances) are \textit{locally scoped}. 
%%%This allows for the same
%%%type to resolve to different values at different points in the
%%%program.  
%Thirdly, the \textit{scope nesting} prioritizes
%implicits. It enables an important and much desired feature without
%satisfactory solution in the globally-scoped type class approach: how
%to override general rules with ad-hoc cases, known as
%\textit{overlapping rules}.  The Scala solution to overlapping rules is
%  to place the ad-hoc cases in a nested scope, prioritizing them over
%  the general rules in an outer scope. 

%% Finally, it is important to 
%% note that while implicits offer many advantages over type classes, 
%% they have significantly less support for type-inference.


\paragraph{Other mechanisms} Other implicit programming mechanisms sit
in between Haskell type classes and Scala implicits in terms of design
choices. For instance, many proposals for \emph{concepts}, from the
(C++) generic programming community, share with type classes the
segregation between (concept) interfaces and other types, but
emphasize local scoping like Scala implicits. Similarly, the proposal
of Dreyer et al.~\cite{modular} for combining ML-style modules and
type classes distinguishes modules (that model type classes) and other
types, and uses local scoping. Most of these proposals, however, do
not allow overlapping rules nor higher-order ones.

%%\end{itemize}

There is a need to shed more light on the implicit
programming design space from a formal point of view. The existing
literature only addresses features like nested scoping, 
overlapping rules and higher-order predicates independently, but 
it does not provide an account of the combination of these features.
Furthermore the important issue of coherency remains essentially unresolved. 

\subsection{Contribution} 
Our contributions are as follows.
\begin{itemize}
\item We present an \emph{implicit calculus} and a polymorphic type
  system that supports all the
  above mentioned features of implicit  programming: 
our type-safe implicit calculus seamlessly integrates nested scoping,
overlapping rules and higher-order predicates, while at the same time
ensuring coherency in the presence of overlapping rules. 

\item Despite its expressivness, our implicit calculus is a 
minimal system, which makes it ideal for the formal study of
resolution and scoping issues that occur in implicit programming
mechanisms. Furthermore, unlike most existing approaches to implicit
programming, whose semantics are defined by translation, 
our implicit calculus' operational semantics enables a direct
soundness proof and programs can be understood independently of the
type system.  

\item We present a type-preserving translation from our calculus to
  System F, as a way to implement our calculus. 

\item Finally, we present a small, but realistic source language,
  built on top of our calculus, that captures the essence and, in some
  ways, goes beyond the Haskell and Scala implicit programming
  practice. We also sketch the type-directed translation from the
  source to implicit calculus and discuss design decisions related to
  type-inference.

\end{itemize}

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
% implicit programming mechanisms.

%Technical results

%%We present and compare two semantics for the implicit calculus: a type-directed
%%elaboration semantics and an operational semantics.  While the former is the
%%traditional approach, the latter is the first of its kind for implicit
%%programming: it enables a direct soundness proof and programs can be understood
%%independent of the type system. Moreover, because resolution happens at runtime,
%%a static type system for the operational semantics can accept more programs
%%than for the elaboration semantics, which performs all of resolution statically.

%%In the static type system, we pay particular attention to the different issues
%%that arise with \textit{overlapping rules}, especially with respect to coherency. 
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
% the coherency property. Finally, we show that the operational semantics 
% proposed by us is a \emph{conservative extension} of the elaboration 
% semantics, allowing more programs to be accepted, while still preserving 
% coherency. 

% With respect to the operational semantics, it is worth remarking that
% it is the first operational semantics in the literature for an
% implicit programming mechanism. Traditionally, the semantics or
% implementation of implicit programming mechanisms has been through
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
% supports features related to implicit programming. Most previous work,
% has typically studied each feature in isolation and has been built
% directly on source languages or core languages that have no built-in
% constructs for supporting implicit programming. For example, with
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
% the scoping and resolution features of implicit programming
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
% \paragraph {Overlapping instances and coherency} Related to scoping is the issue
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
%   controversial in the design of implicit programming
%   mechanisms. While certain implementations of Haskell offer some
%   support for overlapping instances, the semantic foundations of
%   overlapping instances are considered to be quite tricky and there is
%   very little work in that area. Notably a desirable property when
%   dealing with overlapping instances is \emph{coherency}.\bruno{Why 
%   is coherency desirable?}
%   Nevertheless, the experience with
%   Haskell libraries has shown that overlapping instances are useful in
%   practice.\bruno{Again, it may be worth mentioning Scala here,
%     because of the prioritized overlapping implicits, we may also 
%   want to point out that Scala implicits ignore the issue of coherency.}
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
% scoping issues that occur in implicit programming mechanisms. From the
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
% implicit programming mechanisms.
% 
% %Technical results
% 
% We present the type system, an operational semantics as well as 
% an elaboration semantics for the polymorphic rule calculus. The 
% operational semantics is proved sound with respect to the type 
% system, and we show that the elaboration semantics is type 
% preserving. Furthermore, both semantics are shown to have 
% the coherency property. Finally, we show that the operational semantics 
% proposed by us is a \emph{conservative extension} of the elaboration 
% semantics, allowing more programs to be accepted, while still preserving 
% coherency. 
% 
% With respect to the operational semantics, it is worth remarking that
% it is the first operational semantics in the literature for an
% implicit programming mechanism. Traditionally, the semantics or
% implementation of implicit programming mechanisms has been through
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
% source languages with implicit programming constructs, we also 
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
% supports features related to implicit programming. Most previous work,
% has typically studied each feature in isolation and has been built
% directly on source languages or core languages that have no built-in
% constructs for supporting implicit programming. For example, with
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
%% - coherency   


% \subsection{Old Stuff}
% 
% A recent trend in many programming languages is support for
% \emph{implicit programming}.  \emph{Implicit programming} denotes a
% programming style where some values are automatically inferred by
% using available type information. Implicit programming is 
% useful because it allows implicitly passing many
% values that are tedious to explicitly pass it makes 
% the code more readable 
% 
% . because they simply follow 
% the type structure of another argument, or 
% 
% Haskell type classes~\cite{} are the
% most prominent example of implicit programming. With type classes,
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
% Implicit programming is to call functions without giving actual
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
% %   implicit programming}. The use of overloaded entity raises {\it
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
% % framework on implicit programming. Many systems only supports global
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
%   following features of implicit programming:
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
% features of implicit programming using examples. Section
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

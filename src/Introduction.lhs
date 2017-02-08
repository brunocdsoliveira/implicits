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

Programming language design is usually guided by two, often competing, 
goals: \emph{flexibility} and \emph{ease of reasoning}.
Many programming languages aim at providing powerful, 
flexible language constructs that allow programmers to achieve reuse, 
and develop programs rapidely and concisely. Other programming languages aim 
easily reasoning about programs, as well as avoid programming
pitfalls. Very often the two goals are at odds with each other, since 
very flexible programming mechanisms make reasoning harder. 
Arguably the art in programming language design is to combine  
both goals.\bruno{Optional paragraph I guess, but it sets the tone 
for what this paper is about: working out how to deal with the tension
between the flexibility of implicits, and strong reasoning properties
such as coherence.}

Implicit programming (IP) denotes a class of language mechanisms,
which infers values by using type information. Examples of IP
mechanisms include Haskell’s type classes~\cite{}, Scala’s
implicits~\cite{}, JavaGI’s generalized interfaces~\cite{}, C++’s
concepts~\cite{}, Agda's \emph{instance arguments}, Coq's type
classes~\cite{} and others~\cite{}. IP can also be viewed as a form of
(type-directed) program synthesis~\cite{}. The programming is said to
be “implicit” because expressions (e.g., those for function
parameters) can be ommitted and instead provided automaticaly via a
\emph{type-directed resolution} process, producing the necessary
values. Implicit values are either fetched by type from the current
(implicit) environment or constructed by type-directed rules.

Currently there are \bruno{at least?} two schools of thought regarding
the design of IP mechanisms. Haskell's original design for type
classes~\cite{} is guided by the strong reasoning qualities of pure
functional languages. In particular, in purely functional programming,
``\emph{substituting equals by equals}'' is expected to hold. That is,
when given two equivalent expressions then replacing one by the other
in \emph{any context} will always lead to two programs that yield the
same result.  Haskell type classes preserve this property, but not for
free.  Haskell imposes several restrictions on type classes to
guarantee this property. For example, the expression:

> show (read ''3'') == ''3'' 

\noindent where functions |show| and |read| have the types: 

> show :: Show a => a -> String
> read :: Read a => String -> a

\noindent is rejected in Haskell due to \emph{ambiguity} of resolution.



as well some design's that closely follow the original design, treat
type classes as special entities in the language

The design of IP mechanisms has led to heated debate~\cite{} about 
the pros/cons of each mechanisms. On the one hand, traditional type 
classes .... On the other hand implicits... 


Type classes 

Programming language design is often guided by two goals. 
On the hand we want programming languages to be as flexible 
and powerful as they can be.   

Generic programming (GP)~\cite{musser88genericprogramming} is a
programming style that decouples algorithms from the concrete types on
which they operate. Decoupling is achieved through
parametrization. Typical forms of parametrization include
parametrization by type (for example: \emph{parametric polymorphism},
\emph{generics} or \emph{templates}) or parametrization by algebraic
structures (such as a monoid or a group).

A central idea in generic programming is \emph{implicit instantiation}
of generic parameters. Implicit instantiation means that, when generic
algorithms are called with concrete arguments, the generic arguments (concrete types, algebraic
structures, or some other form of generic parameters)
are automatically determined by the compiler.  The
benefit is that generic algorithms become as easy to use as
specialized algorithms. To illustrate implicit instantiation
and its benefits consider a \emph{polymorphic} sorting function:

%if False
Otherwise, without implicit instantiation, the
end-user would have to explicitly provide the generic parameters. This
would not only require additional effort, but also pollute 
programs with many additional arguments throughout.

\paragraph{Example} We illustrate GP, implicit
instantiation and their benefits with a small, but realistic,
use-case: a \emph{polymorphic} sorting function.
%endif

< sort : forall a. (a -> a -> Bool) -> List a -> List a 

with 3 parameters: the type of the elements in
the list (|a|); the comparison operator; and the list to be
sorted. Instantiating all 3 parameters explicitly at every use of
|sort| would be quite tedious.  It is likely that, for a given type,
the sorting function is called with the same, explicitly passed,
comparison function over and over again. Moreover it is easy to infer 
the type parameter |a|.  GP simplifies such calls further by
also inferring the comparison operator.

< isort : forall a . (a -> a -> Bool) => List a -> List a

By using $\Rightarrow$ instead of $\to$, the function |isort| declares that the
comparison function is implicit (that is: automatically inferable).
The function is used as in:

< implicit cmpInt : Int -> Int -> Bool in
< implicit cmpChar : Char -> Char -> Bool in
< implicit cmpPair : forall a b . (a -> a -> Bool, b -> b -> Bool) => (a,b) -> (a,b) -> Bool in
<   (isort [2,1,3], isort [('b',1),('b',0),('c',2)])

The two calls of |isort| each take only one explicit
argument: the list to be sorted. Both the type of the
elements and the comparison operator are \emph{implicitly} instantiated.
The element type parameter is automatically inferred from the type of the input list.
For example in the first |isort| call the element type call is |Int|, whereas 
in the second call the element type is |(Char,Int)|.
More interestingly, the implicit comparison operator is automatically 
determined in a process called \emph{resolution}. Resolution is a type-directed 
process that uses a set of \emph{rules}, the \emph{implicit} (or
\emph{rule}) environment, 
to find a value that matches the type required by the function call. 

The |implicit| construct extends the implicit environment with new rules.
In other words, |implicit| is a \emph{scoping} construct for rules
similar to a conventional |let|-binding. In this example we introduce three 
rules into the implicit environment. Each rule adds a previously defined 
function (here |cmpInt|, |cmpChar| and |cmpPair|) % (whose definitions are not shown here)
to the implicit environment. 

To infer an implicit comparison function for |isort|, the resolution mechanism 
uses the rules in the implicit environment to construct a value of the right type. 
In the first call of |isort| the function |cmpInt| can be used directly because 
it matches the type of the comparison operation needed for that call. 
In the second call of |isort| a comparison function of type 
| (Char,Int) -> (Char,Int) -> Bool | is needed, but no function matches this 
type directly. However it is possible to combine the polymorphic function 
|cmpPair| with |cmpInt| and |cmpChar| to create a function of the desired type.
The ability to compose functions in a type-directed manner illustrates
the real power of the resolution mechanism: a finite set of rules can be used 
to automatically create specific instances at an infinite number of types. 


%%\hfill$\Box$ 

\subsection{Existing Approaches to Generic Programming}

%if False

Generic programming has a long history (see ~\cite{} 
for good, extensive overviews). Most prominently the 
two main lines of work in generic programming are from the 
C++ community and from the functional programming community
(specially Haskell). In the C++ community generic programming 
ideas go back to~\cite{}, which introduced many of the ideas 
associated to generic programming. In the functional programming 
community, type classes    

%endif

The two main strongholds of GP are the C++ and the functional programming (FP)
communities.  Many of the pillars of GP are based on the ideas promoted
by Musser and Stepanov~\shortcite{musser88genericprogramming}. These ideas
were used in C++ libraries such as the Standard Template Library~\cite{musser95stl} and Boost~\cite{boost}. In
the FP community, Haskell \textit{type classes}~\cite{adhoc} have proven to be 
well suited to GP, although their original design did
not have that purpose. As years passed the FP community
created its own forms of GP~\cite{jansson96polytypic,gibbons03patternsin,sybclass}.

Garcia et al.'s~\shortcite{garcia03comparative} comparative study of programming language
support for GP was an important milestone for both communities.  According to that study
many languages provide some support for GP.  However, Haskell did
particularly well, largely due to type classes. A direct
consequence of that work was to bring the two main lines of work on GP
closer together and promote cross-pollination of ideas.  Haskell
adopted \emph{associated types}~\cite{assoctypes,assoctypes2}, which was the only weak point found
in the original comparison.  For the C++ community, type classes
presented an inspiration for developing language support for \emph{concepts}~\cite{musser88genericprogramming,concepts,fg}.

Several researchers started working on various approaches to concepts
(see Siek's work~\cite{siek11concepts} for a historical overview).
Some researchers focused on integrating concepts into
C++~\cite{reis06specifying,concepts}, while others focused on
developing new languages with GP in mind.  The work on System
$F^{G}$~\cite{fg,G} is an example of the latter approach: Building on
the experience from the C++ generic programming community and some of
the ideas of type classes, Siek and Lumsdaine developed a simple core
calculus based on System F which integrates concepts and improves on
type classes in several respects. In particular, System $F^{G}$
supports \emph{scoping} of rules (in the context of C++ rules
  correspond to \emph{models} or \emph{concept\_maps}).

During the same period Scala emerged as new contender in the area of
generic programming. Much like Haskell, Scala was not originally developed with
generic programming in mind.  However Scala included an alternative to
type classes: \emph{implicits}. Implicits were initially viewed as
\emph{a poor man's type classes}~\cite{odersky06poor}. Yet, ultimately,
they proved to be quite flexible and in some ways
superior to type classes. In fact Scala turns out to have fine
support for generic programming~\cite{scalageneric,implicits}.

A distinguishing feature of Scala implicits, and a reason for their
power, is that resolution works for
\emph{any type}. This allows Scala to simply reuse standard OO
interfaces/classes (which are regular types) to model concepts, and avoids introducing another
type of interface in the language.  In contrast, with type classes, or
the various concept proposals, resolution is tightly coupled with the type
class or concept-like interfaces.

%explain this better?
 
%% proposals for concepts interfaces and various other mechanisms
%% restrict resolution to ...

%if False

Over time type classes have influenced the development of 
various language features. These include 
various proposals for \emph{concepts}~\cite{concepts,fg,G} 
Scala's \emph{implicits}~\cite{implicits},
JavaGI's \emph{generalized interfaces}~\cite{javagi},
modular type classes,
and many others~\cite{instanceargs,coqclasses,haftmann06constructive,modular}.
Type classes have also benefited from ideas 

%endif

\subsection{Limitations of Existing Mechanisms}

Twenty years of programming experience have given the FP community
insights about the limitations of type classes. Some of these
limitations were addressed by concept proposals and others by
implicits. We list these limitations next.  As far as we know, no
existing language or language proposal overcomes all limitations, as
our proposal does.

%if False

For example scoping of models 
is one of the thorning issues that has repeatedly pointed out the 
type class literature. However, some other limitations still persist. 

As it turns out the general resolution mechanism from Scala implicits 
reveals itself very useful to overcome the remaining limitations of type 
classes and concept proposals. We discuss the main limitations next:

%endif

%%\begin{itemize}

\paragraph{Global scoping} In Haskell, rules (in 
the context of Haskell rules correspond to \emph{type-class instances}) are global and 
  there can be only a single rule for any given
  type~\cite{named_instance,systemct,implicit_explicit,modular} in the entire program.
  Locally scoped rules are not available. Several researchers 
  have already proposed to fix this issue: with
  named rules~\cite{named_instance} or locally
  scoped ones~\cite{systemct,implicit_explicit,modular}.
  However none of those proposals have been adopted.

  Both proposals for concepts and Scala implicits offer scoping of rules
  and as such do not suffer from this limitation.


\paragraph{Second class interfaces} Haskell type classes are second-class
  constructs compared to regular types: in Haskell, it is not possible to abstract
  over a type class~\cite{restricted}. Yet, the need for
  first-class type classes is real in practice. For example, L\"ammel and Peyton Jones~\shortcite{sybclass} 
  desire the following type class for their GP approach:

< class (Typeable a, cxt a) => Data cxt a where 
<   gmapQ :: (forall b. Data cxt b => b -> r) -> a -> [r]

In this type class, the intention is that the |ctx| variable abstracts over 
a concrete type class. Unfortunately, Haskell does not support type class abstraction.
Proposals for concepts inherit this limitation from type classes. 
Concepts and type classes are usually interpreted as predicates on types rather than types, 
and cannot be abstracted over as regular types. 
In contrast, because
in Scala concepts are modelled with types, 
it is possible to abstract over concepts. Oliveira and Gibbons~\shortcite{scalageneric} 
show how to encode this example in Scala.

\paragraph{No higher-order rules} Finally type classes do not support 
  higher-order rules. As noted by Hinze and Peyton Jones~\shortcite{derivable}, 
  non-regular Haskell datatypes like:

> data Perfect f a = Nil | Cons a (Perfect f (f a))

require type class instances such as:

> instance (forall b. Show b => Show (f b), Show a) => 
>   Show (Perfect f a)

which Haskell does not support, as it restricts
instances (or rules) to be first-order.
This rule is \textit{higher-order} because it assumes another rule, |forall b. Show b =>
Show (f b)|, that contains an assumption itself. Also note that this assumed
rule is polymorphic in |b|.

  Both concept proposals and Scala implicits inherit the limitation of 
  first-order rules. 



%if False

\emph{Concepts} were originally proposed 

Talk about C++ concepts and generic programming

including proposals for language support 
for \emph{concepts}.   

IP has proven its benefits in practice.
Haskell's \emph{type classes}~\cite{adhoc,tchaskell}, 
Scala's \emph{implicits}~\cite{implicits},
JavaGI's \emph{generalized interfaces}~\cite{javagi}, 
C++'s \emph{concepts}~\cite{concepts,fg,G} 
and others~\cite{instanceargs,coqclasses,haftmann06constructive,modular}
are all IP mechanisms. IP
significantly reduces the amount of tedious, explicitly passed
expressions. It models constrained {polymorphism}~\cite{constrained}, and
presents a powerful and disciplined form of {overloading}~\cite{adhoc}.

make a study comparing various languages 
in terms of their support. 

Constrained polymorphism is the space that we are targeting.
Studies show that type-classes are very good in this space. 
Many proposals for concepts are inspired by type-classes. 

Traditional approaches: Type-classes/Concepts:

implicit instantiation + concept interfaces

These interfaces are treated specially by the compiler, 
and usually differ from other types in the language;
implicit instantiation works only for concept interfaces

Scala: A different approach

- Build only implicit instantiation to the language; implicit
instantiation works for any type.  Reuse the notion of interfaces
already built-in (OO interfaces).

Traditional approaches vs Scala: 

A)

Traditional: special treatment of concept interfaces; artificial 
restrictions.

Scala: The fact that implicit instantiation deals with any type,
removes artificial restrictions. No more second-class 
type-classes/concept interfaces; higher-order rules/models.  

B)

Traditional: means additional conceptual and implementation 
overhead: users must understand yet another concept; and compiler 
writers must developed more code to accomodate for similar, but 
not equal types of interfaces.

Scala: more lightweight implementation (though resolution is 
trickier because we have to deal with any type) and less 
conceptual overhead for programmers;

3) Moreover  certain restrictions apply to concept-interfaces and 
type classes (second class).

Scala: A different approach

- build implicit instantiation to the language and reuse the notion 
of interfaces already built-in (OO interfaces). 

- supports many the nice properties that are desirable in a generic
programming language (see OOPSLA paper);

- implemented in a real programming language/compiler (Scala);

- Scala collections library (a widely used application) at the level
of the STL (see Odersky paper). Other libraries: scalaz . Advanced GP: Scala for GP.  

Consequences:

1) implicit instantiation works for any type (not only concept 
interfaces);

2) Removes artificial restrictions. No more second-class type-classes/concept 
interfaces; higher-order rules/models.  

3) The choice of an interface for concepts becomes orthogonal. 
Take modules, and get Modular Type Classes, take OO classes 
and get a Scala model, take structural types and get structural 
concepts.

4) more lightweight implementation (though resolution is 
trickier because we have to deal with any type) and less 
conceptual overhead for programmers;

\subsection{Contributions}

%%Higher-order rules allow increased 
%%expressiveness in much in the same way that higher-order functions  
%%allow increase expressivness over first-order functions.

However, unlike any languages that we know of, we support 
higher-order rules.


Furthermore, the values available for 
resolution are controlled by scoping mechanisms

Candidate values to be used by resolution 
are adde

The language has scoping constructs (analogous 
to lambda abstractions) that 
allow values of a any type to be added to the implicit environment.  


A minimal and general calculus for implicits, which captures the
essential notions of implicits: type-directed resolution + implicit 
scoping. Furthermore the calculus offers new expressive power: 
higher-order rules (models),  which haven't been covered in any 
of the existing approaches. Scoping? First-class concepts - shown 
to be useful in the literature. 

Problem:

Scala: Scala compiler, libraries, but no formalism. 

Type classes: several implementations, many libraries, with corresponding formalisms. 

Concepts: Formalisms like SystemF$^G$, proposals for concepts, ConceptGCC

So, we want to show why first-class concepts are good

and how we support that

guess we can use the Syb example, or maybe Collections with different constraints on the arguments

the 2nd maybe easier to digest by the audience
Tom Schrijvers 10/17/11 2:31 PM 
From a language design point of view, the extra set of interface types is also incidental complexity.

\subsection{Old intro}



Implicit programming (IP) infers values by using type information. It is
``implicit'' because we can omit expressions (e.g., those for function
parameters) and instead rely on type-directed resolution to produce the
necessary values. 
%mentioning a type does not explicitly pinpoint a
%value by an expression but just means a value of that type.
Implicit values are either fetched by type from the current (implicit)
environment or constructed by type-directed \emph{rules}. 

IP has proven its benefits in practice.
Haskell's \emph{type classes}~\cite{adhoc,tchaskell}, 
Scala's \emph{implicits}~\cite{implicits},
JavaGI's \emph{generalized interfaces}~\cite{javagi}, 
C++'s \emph{concepts}~\cite{concepts,fg,G} 
and others~\cite{instanceargs,coqclasses,haftmann06constructive,modular}
are all IP mechanisms. IP
significantly reduces the amount of tedious, explicitly passed
expressions. It models constrained {polymorphism}~\cite{constrained}, and
presents a powerful and disciplined form of {overloading}~\cite{adhoc}.

\paragraph{Example}
As a small, but realistic use-case of IP, consider a
non-implicit, \emph{polymorphic} sorting function:

< sort : forall a . (a -> a -> Bool) -> List a -> List a 

%IP offers a convinient way to define such a
%function. Sorting cannot be defined as a purely parametric polymorphic
%of type |forall a. List a -> List a|, because it needs to know how to
%compare the elements of the list. However \emph{explicitly} passing a
%comparison function, can be very tedious: it is likely that for a
%given type the sorting function is called with the same comparison
%function over and over again. By using an implicit argument for 
%passing the comparison function around this problem can be elimated. 
%
A comparison operator must be
passed explicitly with every use of |sort|. This explicit style of programming
can be tedious; it is likely that, for a given type, the sorting
function is called with the same, explicitly passed, comparison function 
over and over again. IP simplifies such calls
by making the argument implicit.

< isort : forall a . (a -> a -> Bool) => List a -> List a

The function |isort| declares that its first argument is implicit by using
$\Rightarrow$ instead of $\to$. It is used as:

< implicit {cmpInt : Int -> Int -> Bool} in
<   (isort [2,1,3], isort [5,9,3])

The two calls of the |isort| function
each take only one explicit argument: the list to be sorted.  The comparison
operator (|cmpInt|) is \emph{implicitly}
passed. This implicit parameter is looked up automatically from the implicit environment in
a process called \emph{resolution}. The |implicit| construct is a
\emph{scoping} construct analogous to a |let|-binding. It extends the
implicit environment by bringing the |cmpInt| function into the scope
of the body expression  | (isort [2,1,3], isort [5,9,3]) |. 
\hfill$\Box$

In this paper we present $\ourlang$: a general and expressive, yet
minimalistic, polymorphic calculus that is suitable for studying the
essence -- \emph{scoping} and \emph{resolution} -- of IP. Because IP
mechanisms are often studied in the context of larger source
languages, scoping and resolution do not get the attention they
deserve and are (artificially) restricted to suit the needs of the
particular source language. Our calculus is not bound by the
intricacies of any source language. This enables it to tackle
the important IP issues, and shed new light on the design of IP
mechanisms.

The remainder of this section provides an overview of our IP calculus
$\ourlang$~(Section ~\ref{subsec:over}), exposes problems and
limitations of existing IP practice~(Section ~\ref{subsec:problem}),
and summarizes our contributions~(Section
~\ref{subsec:contributions}).

%-------------------------------------------------------------------------------
\subsection{Problem}\label{subsec:problem}

All the features presented in Section~\ref{subsec:over} are known to be useful
for IP~\cite{derivable,sybclass,scalageneric,quantified}. Yet, no IP mechanism that we
know of supports them all. Many features have been studied independently, and
have only been informally discussed.

\paragraph{Type classes} Haskell's {type classes}~\cite{adhoc}, the most
prominent IP mechanism, explore only a particular corner of the large IP
design space~\cite{designspace}. They have three notable limitations:

\begin{itemize}

\item Haskell's resolution rules are global. Hence, there can only be
  a single rule for any given
  type~\cite{named_instance,systemct,implicit_explicit,modular}.
  Locally scoped rules are not available. Several researchers 
  have already proposed to fix this issue: with
  named rules~\cite{named_instance} or locally
  scoped ones~\cite{systemct,implicit_explicit,modular}.
% Kahl and Scheczyk~\cite{named_instance} proposed to address this
%problem with \emph{named instances}, offering the possibility to name
%instances and manually select instances for resolution using these
%names. Others have suggested mechanisms that allowed
%\emph{local scoping} of
%instances~\cite{systemct,implicit_explicit,modular}, thus
%offering control over which instances are on scope rather than having
%a single global scope. 
%

\item Haskell type classes are second-class
  constructs compared to regular types: in Haskell, it is not possible to abstract
  over a type class~\cite{restricted}. Yet, the need for
  first-class type classes is real in practice. For example, L\"ammel and Peyton Jones~\shortcite{sybclass} 
  desire the following type class for their GP approach:

< class (Typeable a, cxt a) => Data cxt a where 
<   gmapQ :: (forall b. Data cxt b => b -> r) -> a -> [r]

In this type class, the intention is that the |ctx| variable abstracts over 
a concrete type class. Unfortunately, Haskell does not support abstraction
over type classes.

\item Finally, type classes do not support higher-order rules. As noted
  by Hinze and Peyton Jones~\shortcite{derivable}, non-regular Haskell
  datatypes like:

> data Perfect f a = Nil | Cons a (Perfect f (f a))

(a variation of the well-known perfect tree type) require type class
instances such as:

> instance (forall b. Show b => Show (f b), Show a) => 
>   Show (Perfect f a)

which Haskell does not support, as it restricts
instances (or rules) to be first-order.
This rule is \textit{higher-order} because it assumes another rule, |forall b. Show b =>
Show (f b)|, that contains an assumption itself. Also note that this assumed
rule is polymorphic in |b|.  

%if False

In $\ourlang$ such
higher-order rules are allowed:
 
< forall f a . {forall b. {Show b} => Show (f b), Show a} 
<               =>  Show (Perfect f a)

%endif

\end{itemize}

%Finally, type class
%constraints consist, essentially, of first-order rules, %predicates on types,
%but for some applications \emph{higher-order rules} are %predicates} are
%needed~\cite{derivable,scalageneric}.

\paragraph{Scala implicits} Scala implicits~\cite{implicits}
are an interesting alternative in IP
design. Unlike type classes, implicits have locally scoped rules. Moreover,
values of any type can be used as implicit parameters; there is no special 
separate type-class-like interface. Instead, such interfaces are
modelled with regular types, they can be abstracted over and do 
not suffer from the second class nature of type classes. In $\ourlang$
we also make similar design choices.

%format v1 = "\Varid{v_1}"
%format v2 = "\Varid{v_2}"

\begin{figure}
\small
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

However, implicits have been described only informally~\cite{implicits,scala}
and some of the design decisions are quite ad hoc. In particular, 
although Scala allows \emph{nested} local scoping and overlapping rules,
\textit{coherence} is not guaranteed. Figure~\ref{fig:scala} illustrates
the issue briefly, using the example that was presented in
Section~\ref{subsec:over}. Scala's subclassing creates nested
implicit scopes. The program is accepted, but Scala incoherently
selects the more general implicit value (|id|) for |v1|. In contrast, |v2|,
which (naively) inlines |func[Int]|, picks |succ|. As a result, despite
looking equivalent, the two expressions yield different results.
This makes such programs quite hard to understand. 

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


\paragraph{Other mechanisms} Other IP mechanisms sit
in between Haskell type classes and Scala implicits in terms of design
choices. For instance, many proposals for \emph{concepts}~\cite{concepts,fg,G}, from the
(C++) generic programming community, share with type classes the
segregation between (concept) interfaces and other types, but
emphasize local scoping like Scala implicits. Similarly, the proposal
of Dreyer et al.~\shortcite{modular} for combining ML-style modules and
type classes distinguishes modules (that model type classes) and other
types, and uses local scoping. 

%%\end{itemize}

More generally, there are two features that are not supported by any 
IP mechanism that we know of: \emph{higher-order rules} and
\emph{coherent support for overlapping rules} arising from nested 
scoping.

There is a need to shed more light on the implicit
programming design space from a formal point of view, specially with respect 
to scoping and resolution aspects. The existing
literature only addresses features like local and nested scoping, 
overlapping rules and higher-order predicates independently, but 
it does not provide an account of the combination of these features.
Furthermore the important issue of coherence remains essentially unresolved. 

%endif

%-------------------------------------------------------------------------------
\subsection{Contributions}\label{subsec:contributions}

This paper presents $\ourlang$, a minimal and general core calculus
for implicits and it shows how to build a source language supporting
implicit instantiation on top of it. Perhaps surprisingly the core
calculus itself does not provide implicit instantiation: instantiation
of generic arguments is explicit. Instead $\ourlang$ provides two key
mechanisms for generic programming: 1) a type-directed resolution
mechanism and 2) scoping constructs for rules. Implicit instantiation
is then built as a convenience mechanism on top of $\ourlang$ by combining type-directed
resolution with conventional type-inference.  We illustrate support for implicits
with a simple source language.

The calculus is inspired by Scala implicits and it
synthesizes core ideas of that mechanism formally. In
particular, like Scala implicits, a key idea is that resolution and
implicit instantiation work for any type. This allows those mechanisms 
to be more widely useful and applicable, since they can be used with
other types in the language.
The calculus is also closely related to System $F^G$, in that rules available in the
implicit environment are lexically scoped and scopes can be nested.

A novelty of our calculus is its support for partial resolution and higher-order rules. 
Although Hinze and Peyton Jones~\shortcite{derivable} have discussed higher-order rules informally 
and several other researchers noted their usefulness~\cite{trifonov03simulating,rodriguez08comparing,scalageneric}, no existing 
language or calculus provides support for them. Higher-order rules 
are just the analogue of higher-order functions in the implicits 
world. They arise naturally once we take the view that resolution 
should work for any type. Partial resolution adds additional expressive 
power and it is especially useful in the presence of higher-order rules.

%% \bruno{Needs polishing} 
From the GP perspective $\ourlang$
offers a new foundation for generic programming. 
The
relation between the implicit calculus and Scala implicits is
comparable to the relation between System $F^G$ and various
concept proposals; or to the relation
between formal calculi of type classes and Haskell type classes: The 
implicit calculus is a minimal and general model of implicits useful for language
designers wishing to study and inform implementations of similar GP mechanisms in
their own languages.


%if False

is interesting because 
it decouples resolution from concepts. This makes the mechanism: 
1) more general and widely useful; 2) more lightweight in terms of 
implementation. Because resolution is not limited to concepts, 
other types can also be used during resolution.
big ongoing debate on what the right form of concept interfaces should 
be for generic programming (structural vs. nominal, OO classes vs. 
concepts vs. type-classes). 
Of course this also means that a little more effort needs to go into 
the source language when compared to System F$^G$.
By modelling concepts as types there's less conceptual bagage, and 
implementations can avoid certain redundancies in the language.  

%endif


In summary, our contributions are as follows.

\begin{itemize}
\item Our \emph{implicit calculus} $\ourlang$ 
  provides a minimal formal model for implicits, which can be used 
  for the study of implicits and GP.
%% integrates 
%%  nested scoping and it supports partial resolution and higher-order rules
%%  Despite its expressiveness, the
%%  calculus is minimal and provides an ideal setting for the formal
%%  study of implicits and GP.

\item Our resolution mechanism is more expressive than existing mechanisms 
  in the literature. It works for any type, supports local scoping, first-class 
  interfaces, higher-order rules, as well as partial resolution.
  The mechanism is based on unification and resembles logic programming.

%%Of particular interest is our resolution mechanism, which is 
%%  significantly more expressive than existing mechanisms 
%%  in the literature. It is based on a simple (logic-programming style) query language, 
%%  works for any type, and it supports partial resolution as well as higher-order rules.

%%\begin{itemize}
\item We provide a semantics in the form of a translation from $\ourlang$
   to System F. We prove our translation to be type-preserving, ensuring soundness.
   The translation also serves as an effective implementation technique.

%%The calculus has a polymorphic type system and an elaboration 
%%  semantics to System F. This also provides an effective implementation 
%%  of our calculus. The elaboration semantics is proved to be type-preserving, 
%%  ensuring the soundness of the calculus.

%if False

\item In contrast to most existing IP approaches that only have
  an elaboration semantics, we present an operational semantics for
  $\ourlang$ (Section~\ref{subsec:opsem}). The operational semantics
  enables a direct soundness proof, and programs can be understood
  independently of the type system. \tom{don't mention operational semantics anymore}

%endif

\item We present a small source language
  built on top of $\ourlang$ via a type-directed encoding,
  to demonstrate how $\ourlang$ supports implicit instantiation and 
  can be used to model concepts with higher-order rules.

%% This language features implicit instantiation 
%%  and a simple type of interface, which can be used to model simple forms of 
%%  concepts. This source language also supports higher-order rules.
 %%This language is expressive enough to capture the essence
  %%of GP practice, in some ways it goes beyound that practice. 

\item Finally, both $\ourlang$ and the source language have been
  implemented and the source code for their implementation is available
  at \url{http://i.cs.hku.hk/~bruno/implicit}. 

\end{itemize}


%-------------------------------------------------------------------------------
\paragraph{Organization} 
Section 2 presents an informal overview of our calculus. 
Section 3 describes a polymorphic type system that
statically excludes ill-behaved programs. Section 4 provides the elaboration 
semantics of our calculus into System F and correctness results. 
Section 5 presents the source language and its encoding into $\ourlang$. 
Section 6 discusses comparisons and related work. Section 7 concludes.

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

%include lhs2TeX.fmt
%include Scala.fmt

\section{Related Work}
\label{sec:related}

%%This section discusses related work.
%
%In Section~\ref{subsec:problem} we have already discussed the main
%distinguishing factors between our work and Haskell's type classes, Scala's 
%implicits, and some other systems. In what follows, 

We first summarize how our work is in general different from existing
work and then compare in more detail our work with existing work with
respect to scoping, overlapping, coherence, semantics and resolution. 
%
%% \subsection{Scoping and Resolution}

Our work distinguishes itself from previous work in several respects. 
We capture the key features of 
IP in a minimalist and core calculus $\ourlang$. The calculus
shows a seamless integration of a number of
IP features --- local and nested scoping;
higher-order rules and queries; and overlapping rules --- that have
only been studied in isolation before. Furthermore, the calculus'
minimalistic and core nature makes it an ideal platform for a study of
key issues in IP such as scoping and resolution. In contrast,
most existing IP mechanisms have been implemented or
studied as part of a larger source language, hence some artificial restrictions
that are imposed by the intricacies of the source language, which makes the
study of issues such as scoping and resolution hard. 
Finally, thanks to the calculus we can understand and address the
problem of ensuring coherence in the presence of overlapping rules and
nested scoping. 

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
Its most distinctive feature in comparsion with Scala is that it supports
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

%endif

%
%
%%if False
%
%The fact that $\ourlang$ does not provide a special type of ``type
%class'' interface, does not preclude the definition of source
%languages which have such interfaces. In fact, $\ourlang$ is a
%good target language for a language with type classes, or some other
%form of interfaces (such as modules or object-oriented classes).  The
%main challenges of provide a source language with type classes are
%type-inference and subclassing. In Section~\ref{} we have already
%discussed how the issue of type-inference can be overcome for a simple
%language with records. In a source language with type classes, type
%inference could be dealt pretty much in the same way. Furthermore,
%subclassing is not hard to translate to $\ourlang$~\bruno{Tom, say
%  more about this?}. 
%
%Another advantage of allowing any types in resolution is that
%higher-order predicates come essentially for free. Since we can query
%any types and have any types in the implicit environment, supporting
%higher-order predicates amounts to allowing polymorphic rule types to
%be queried.
% 
%One way in which our calculus is closer to type classes is that 
%implicit arguments are sets rather than lists (as in Scala). 
%
%> let f : {Int} => 
%
%> let f   
%
%Compared with type classes, this
%design is, in some sense, more primitive as it  
%
%and it has some drawbacks in terms of usability. Namely and refinement
%(subclass) relations between class interfaces allow programmers to
%express certain constraints more conveniently. Scala implicits are
%expressive enough to encode the same essential programming patterns
%expressible with types classes~\cite{implicits}, but the encoding can
%make the programming-style more low level than type classes due to
%type-inference limitations, and the need to encode subclassing.
%
%Usability concerns are not so important in a core calculus, where
%expressiveness and simplicity of the design are more relevant. 
%
%By allowing any types to be involved in the resolution process, 
%the implicit calculus  
%
%%endif
%
%%%Another important different to previous work is the minimalistic 
%%%and core nature of our calculu
%
%%if False
%
%% Scoring:
%\newcommand{\scri}[1]{\quad\small #1}% sub-criterion
%\newcommand{\scgood}{\CIRCLE}% good
%\newcommand{\scsuf}{\LEFTcircle}% sufficient
%\newcommand{\scbad}{\Circle}% bad
%
%\newcommand{\latexhline}{\hline}
%
%\begin{figure*}
%\tabcolsep\arraycolsep
%\def\tallstrut{\vrule width0pt height 2.5ex}
%\def\deepstrut{\vrule width0pt height 0pt depth 1.5ex}
%\begin{center}
%\begin{tabular}{l||c||cccc||ccc||cc||c}
%& \multicolumn{1}{c}{\textit{Scala}} & \multicolumn{4}{c}{\textit{Type Classes}} & \multicolumn{3}{c}{\textit{Overloading}} &  \multicolumn{2}{c}{\textit{Others}} & \multicolumn{1}{c}{\textit{$\ourlang$}} \\
%                                          &                 & Wad89       & \textit{Kah01}     & \textit{Dij05}  & \textit{Dre07}    & \textit{O} & \textit{CT} & \textit{Sul05} & \textit{Lew00} & \textit{Gar05} & 
%\deepstrut \\
%\latexhline % ---------------------------------------------------------------
%\tallstrut
%Design choices:                                 &                 &             &                    &                 &                   &                  &                &                &                &           & \\
%\scri{Overloaded Entities}                & Type            & Name        &  Name              & Name            & Name                 & Name             & Name           & Name           & Name              & Name        & Type \\
%\scri{Constraint Semantics}               & [T]             & \{C\}       &  [C$\mid$\{C\}]        & [C]           & \{M\}             & \{N$\times$T\}   & \{N$\times$T\} & \{N$\times$T\} & \{N$\mapsto$T\}& -        & \{T\}   \\
%% \scri{First-class Types}                  & \scgood         & \scbad      &  \scbad            & \scbad          & \scbad            & \scgood          & \scgood        & \scgood        & \scgood        & \scbad  & \scgood \\
%\scri{Implicit Values}                    & \scgood         & \scbad      &  \scbad            & \scbad          & \scbad            & \scgood          & \scgood        & \scgood        & \scgood        & \scbad  & \scgood \\
%\scri{Any Values}                         & \scgood         & \scgood     &  \scgood                 & \scgood               & \scgood           & \scbad           & \scgood        & \scgood        & \scgood              & \scbad        & \scgood \\
%\scri{Overloaded Results}                 & \scgood         & \scgood     &  \scgood                 & \scgood               & \scgood           & \scbad           & \scgood        & \scgood        & -              & \scbad   & \scgood \\
%Resolution:                                    &                 &             &                    &                 &                   &                  &                &                &                &           & \\
%\scri{Recursive Resolution}               & \scgood         & \scgood     &  \scgood           & \scgood         & \scgood           & \scgood         & \scgood              & \scgood       & \scbad         & \scgood        & \scgood \\
%\scri{Higher-order Predicates}               & \scbad             & \scbad       &  \scbad        & \scbad           & \scbad             & \scbad   & \scbad & \scbad & \scbad & \scbad        & \scgood   \\
%% \scri{Contextual Overloading}             & \scbad          & \scbad      &  \scbad            & \scbad          & \scbad            & \scbad           & \scgood        & \scbad         & -         & -        & \scbad \\
%% \scri{Polymorphic Type}                   & \scgood         & \scgood     &  \scgood                 & \scgood               & \scgood           & \scgood          & \scgood         & \scgood        & \scbad              & -     & \scgood \\
%Scoping:                                    &                 &             &                    &                 &                   &                  &                &                &                &           & \\
%\scri{Lexical Scoping}                    & \scgood         & \scbad      &  \scbad            & \scgood         & \scgood           & \scbad           & \scgood        & \scbad         & \scgood        & \scgood  & \scgood \\
%\scri{Nested Scoping}                     & \scsuf          & \scbad      &  \scbad            & \scgood         & \scbad           & \scbad           & \scgood         & \scbad         & \scgood        & \scgood  & \scgood \\
%\scri{Overlapping}                       & -         & -      &  -            & -         & -           & -           & -         & -         & -        & -  & - \\
%Semantics and Coherence:                                    &                 &             &                    &                 &                   &                  &                &                &                &           & \\
%\scri{Coherence}                         & -         & -      &  -            & -         & -           & -           & -         & -         & -        & -  & - \\
%\scri{Resolution Time}                & -         & -      &  -            & -         & -           & -           & -         & -         & -        & -  & - \\
%\scri{Semantics}                          & -               & E           & -                  & E               & E                 & E/D              & -              & E              & E/A            & -        & O/E     \\     
%Source Language:                                    &                 &             &                    &                 &                   &                  &                &                &                &           & \\
%\scri{Overriding}                         & \scgood         & \scbad      &  \scgood           & \scgood         & \scbad           & \scbad           & \scsuf         & \scbad         & \scgood        & \scbad & \scsuf       \\
%\scri{Constraint Inference}               & \scbad          & \scgood     &  \scgood           & \scgood         & \scgood                 & \scgood          & \scgood        & \scgood        & \scgood        & -        & \scgood \\
%\scri{Context Reduction}                  & \scbad          & \scgood     &  \scbad           & \scgood         & \scgood           & \scbad         & \scgood              & \scgood       & \scbad         & -        & \scgood \\
%\scri{Late Binding}                       & \scgood         & \scbad      &  \scgood           & \scgood               & \scgood                 & \scbad           & \scbad         & \scbad         & \scbad         & \scgood  & \scgood \\
%%%Others:                                    &                 &             &                    &                 &                   &                  &                &                &                &           & \\
%%%\scri{Flexible Type                     & -               & \scbad      &  \scbad                 & \scbad               & \scbad                 & \scgood          & \scsuf             & \scbad         & -              & -        & - \\
%%%\latexhline % ---------------------------------------------------------------
%%%Formalization:                            & \scbad          & \scgood     & \scsuf             & \scsuf          & \scgood           & \scgood          & \scsuf         & \scgood        & \scgood        & \scbad   & \scgood \\
%%%\scri{Metatheory Results}                 & -               & \scgood     & \scsuf             & \scbad          & \scgood           & \scgood          & \scsuf         & \scgood        & \scgood        & -        & \scgood \\     
%%%\scri{Machine Checked}                    & -               & \scbad      & \scbad             & \scbad          & \scbad            & \scbad           & \scbad         & \scbad         & \scbad         & -        & \scgood \\     
%\deepstrut \\
%\end{tabular}
%\end{center}
%
%\begin{tabular}{c||c}
%Abbreviations used in the Constraint semantics row & Abbreviations used in the Semantics row \\
%\begin{tabular}{c||l}
%T & Type\\
%C & Type Class\\
%M & Module\\
%N & Name\\
%\end{tabular}&
%\begin{tabular}{c||l}
%E & Elaboration Semantics\\
%A & Axiomatic Semantics\\
%D & Denotational Semantics\\
%O & Operational Semantics\\
%\end{tabular}\\
%\end{tabular}
%
%\caption{The design space of mechanisms related to implicit
%  programming.\bruno{Need to adapt the figure to fit with the
%    structure of the overview.}}
%\label{fig:evaluation}
%\end{figure*}
%
%To aid with the comparison to related work we summarize the features  
%available in various systems in Figure~\ref{}, and compare it with our 
%own work. In the table, only features related to scoping and
%resolution are discussed. 
%
%%endif

\paragraph{Scoping, Overlapping, and Coherence}
%Several works have discussed scoping mechanisms for IP. 
Our work allows nested scoping with overlapping rules
while guaranteeing coherence. Regarding these issues, previous
approaches can be divided into two types. The first type of
approaches allow local scoping but forbid nested scoping and, as
such, avoid the issue of guaranteeing coherence in the presence of
overlapping. Modular type
classes~\cite{modular} and System $F_{G}$~\cite{systemfg} are examples of
such approaches. The second type of approaches allow nested scoping,
but do not guarantee coherence. Most prominently, Scala falls in this
category, but there are several other proposals that also follow such
approach~\cite{systemct,implicit_explicit,instanceargs}.

The GHC Haskell compiler supports overlapping instances~\cite{designspace},
that live in the same global scope. Our calculus generalizes this idea to
local scoping. The problem with GHC's scope is that deciding coherence requires
global information. This is at odds with modular compilation. As GHC prefers
the latter, it does not perform a full coherence check and thus cannot
guarantee coherence across modules.

Our calculus is different from \emph{instance chains}~\cite{chain}
too. With instance chains the programmer imposes an
order on a set of overlapping type class instances. All instance
chains for a type class have global scope and are expected not to
overlap. This makes the scope of overlapping closed within a chain,
which is one way to ensure the coherence under the presence of
overlap. In our calculus, we make our local scope closed,
thus overlap only happens within one nested scope.

Lastly, Jones~\cite{coherence_qual} discussed about the coherence of
qualified type system in his work on qualified types. In their
definition, the translation semantics is coherent if the given
system of predicates guarantees the uniqueness of evidence. Their coherence
provides a general framework for Haskell-like systems, but it leaves
out the details about how to coherently generate the evidence, which
is non-trivial with overlapping instances.

\paragraph{Semantics}
%\bruno{This paragraph needs to be rewritten!}

Our calculus' dynamic semantics is defined in a big-step operational
semantics. This contrasts with the majority studies of IP mechanisms.
The majority have a semantics based on translation,
in which the queries are resolved statically. Several
researchers~\cite{tchaskell,snd_over} have pointed out that an
translation semantics is a weakness of those systems: the static and
dynamic semantics cannot be understood independently, and there is no
semantic soundness result. Though Thatte's work~\cite{semantics_typeclass},
which is one exception, translates a program with type classes
into one of an ML-like calculus with typecase and fixpoint
operator, the resolution in the translated program is done
dynamically. Still the work suffers from having no direct soundness
result with respect to the dynamic semantics.

There is a few other works that provide a dynamic semantics for IP,
but they have some restrictions that our calculus' operational
semantics does not. Notable such works are by Odersky et
al. \cite{snd_over} and Kaes \cite{kaes}. Their systems provide
both translation and denotational semantics for their overloading
mechanisms. % As as far as we know, $\ourlang$ is
% the third system provides dynamic semantics as a foundation for type
% system and translation. 
% Kaes's work \cite{kaes} is one of the earliest work in the type class
% field. 
However, Kaes's system does not 
support overlapping, local scoping and polymorphic instances. 
Odersky et al.'s system, cannot make instances that are polymorphic
on the return type. Besides, their dynamic semantics require runtime
type information to resolve overloaded instances. Our operational semantics, on
the contrary, has none of these restrictions and does not need to
check the type of value at runtime. 

%\bruno{Shouldn't
%  the point here be the fact that our operational semantics does *not* dependent 
%on the static semantics, whereas their dynamic semantics *depends* on
%the static semantics.}

%However the dynamic semantics is still coupled with the
%static semantics. (some amount of type-checking is needed at
%run-rime). \bruno{Others?}

%The implicit calculus distinguishes also does have an operational semantics. In
%this operational semantics types cannot be erased. However, the operational
%semantics itself is independent of the type system and we can prove semantic
%soundness.

%Our operational semantics has an additional advantage: it features run-time
%resolution. In the presence of overlapping instances, this allows us to accept
%more programs than the elaboration semantics.
%\wt{This is not true any more}

%\bruno{Say more about related work``typecase'' stuff; Kaes?}
%
%\bruno{Do we want to go into details? Probably not, but if we want we
%  can add the text below.}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Resolution}
Resolution in $\ourlang$ is significantly more expressive than in
other systems. Notably resolution supports higher-order rule types and
queries, as well as queries for polymorphic types. A closely related
design is that of higher-order predicates by Hinze and Peyton
Jones~\cite{derivable}. However, similar extensions have not been
adopted by any other IP systems.

As such, the interaction with other features is first studied by our work.
Notably, Hinze and Peyton Jones propose the more expressive resolution rule,
but do not consider our main reason for adopting a simpler definition: its
impact on guaranteeing coherence in the presence of overlap (as well as
guaranteeing termination).

As Hinze and Peyton Jones show, higher-order predicates are specially important
when dealing with types that involve type constructor polymorphism. In order to
simplify presentation, our formalization of the implicit calculus does not
include type constructor polymorphism. However, such an extension is
straightforward, as our implementation shows.

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
modular type classes and instance arguments~\cite{instanceargs} in Adga shows that,
when a good notion of interfaces exists in the base language, the
addition of an IP mechanism makes many advanced
features such as associated types fall out essentially for free.


%%% Local Variables: 
%%% mode: latex
%%% TeX-master: "../Main"
%%% End: 

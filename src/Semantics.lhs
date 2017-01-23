
%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Rule.fmt

%format === = "\cong"

\section{The $\ourlang$ Calculus}
\label{sec:ourlang}

This section presents the syntax and operational semantics 
of $\ourlang$. Our calculus $\ourlang$ combines standard scoping mechanisms 
(abstractions and applications) and types \`a la System F, with a
logic-programming-style query language. 
At the heart of the language is a threefold interpretation of types:
\begin{center}
  |types === propositions === rules|
\end{center}
\noindent Firstly, types have their traditional meaning of classifying
values.  Secondly, via the Curry-Howard isomorphism, types can
also be interpreted as propositions -- in the context of IP, the type
proposition denotes the availability in the implicit environment of a
value of the corresponding type. Thirdly, a type is interpreted as a
logic-programming style rule, i.e., a Prolog rule or Horn
clause~\cite{kowalski}.
%%\footnote{The connection between type class
%%  instances and Prolog rules is folklore.}
Resolution~\cite{resolution} connects rules and propositions: it is
the means to show (the evidence) that a proposition is entailed by a set of rules.
%%Again, a value serves as evidence for the rule interpretation,
%%constructing a proof of one proposition in terms of proofs of others.

%-------------------------------------------------------------------------------
\subsection{Syntax}    
\label{subsec:syntax}
%%$\ourlang$ is a minimal calculus that models a query language,
%%resembling a simple logic programming language. 

The syntax of the calculus is shown next:
{\small \bda{llrl}
    \text{Types} & \type \hide{\in \meta{Type}} & ::=  & \alpha \mid \rulet \\
    \text{Rule Types} & \rulet \hide{\in \meta{RType}} & ::= & 
    \rulesch{\alpha}{\rulesetvar}{\type} \\
    \text{Context} & \rulesetvar \hide{\in 2^\meta{RType}} & ::= & 
    \nil \mid \bar{\rulet} \\
    \text{Expressions} & |e| & ::=  &
    |(query rulet)| \mid 
    | rule (rulet) (e)| \mid
    e[\bar{\type}] \mid
    |e with rulesetexp| \\
  \eda }
Types $\type$ are either type variables $\alpha$ or rule types
$\rulet$.  A rule type $\rho = \rulesch{\alpha}{\rulesetvar}{\type}$
is a type scheme with universally quantified variables $\bar{\alpha}$
and an (implicit) context $\rulesetvar$. We use an overline
to denote a set of entities, like $\bar{\alpha}$. The context is simply 
a set of rule types, which summarizes the assumed implicit environment. We
usually omit empty universal quantifiers and contexts from a rule
type. 

There are four forms of expression. A query |(query rulet)| queries
the implicit environment for a value of type $\rulet$.  A rule
abstraction \\ |rule (rulety) (e)| builds a rule whose type is |rulety|
and whose body is $e$. Rule abstraction has double roles as
a binding structure: 1) the universal quantification of type variables
binds types, and 2) the context binds a rule set. These binders are
respectively eliminated by type application $e[\bar{\type}]$ and rule
application |e with rulesetexp|. 
% \hide{\bruno{old explanation here.} The main reason why we merged
% two binding structures into one is that we need the information of
% type variables and context at the same time when we match a rule in
% resolution. If we split a rule into multiple constructs, the
% resolution becomes very complex.}

While System F traditionally separates type and value binders in separate
constructs $\Lambda$ and $\lambda$, they belong naturally together in our
interpretation of rules as logic programming rules.\footnote{In Prolog these
are not separated either.} After all, in the matching process of resolution, a
rule is applied as a unit.  Hence, separating rules into more primitive binders
(\`a la System F's type and value binders) would only complicate the definition
of resolution unnecessarily.

% Following the
% interpretation of types as rules, a rule type $\forall \bar{\alpha}.\pi \To
% \type$ combines 3 components: a universal quantifier of type variables
% $\bar{\alpha}$, a left-hand side $\pi$ of assumptions and a right-hand side
% $\type$ which is the consequent of the rule.
% %
% While these three components belong naturally together in $\ourlang$, they
% would be separated in System F, which does not assume a rule interpretation of
% types. Indeed, in System F, a rule like
% 
% %{
% 
% %format blambda = "\Lambda\!"
% %format # = "."
% 
% > rule (forall a b . {a,b} => Pair a b) ((query (Pair a b)))
% 
% would correspond to a term like:
% 
% > blambda a # blambda b # \(x : a) # \(y : b) # (x,y) 


%if False
For brevity of presentation, we put two restrictions in our syntax; 1)
all type variables are distinct. 2) we do not allow two different
expressions for the same rule type in $\rulesetexp$ of rule
application, where ``same'' means syntactically equal up to alpha
convergence of quantified type variables. For example,
$\ruleapp{f}{\myset{\relation{x}{\forall a. a \to a},
    \relation{y}{\forall b. b \to b}}}$ is invalid.
%endif

For brevity $\ourlang$ only concerns IP constructs. In examples we
often use additional syntax such as $\lambda$-binders, integer
and boolean literals and their corresponding types. Extending this
calculus with support for \emph{higher-kinded polymorphism} in the
style of System $F_{\omega}$ is straightforward.  The implementation
of the source language (and $\ourlang$) presented in
Section~\ref{sec:example} implements various of these extensions.

%-------------------------------------------------------------------------------

%if False

\subsection{Motivating the Design of $\ourlang$}

The design of $\ourlang$ combines standard scoping mechanisms (rule
abstractions and applications) and types \`a la System F, with a
logic-programming-style query language. 
At the heart of the language is a threefold interpretation of types:
\begin{center}

> types == propositions == rules 

\end{center}
Firstly, types have of course their traditional meaning of classifying values.
Secondly, following the Curry-Howard isomorphism, type can also be interpreted
as propositions -- in the context of IP, the type proposition denotes the
availability in the implicit environment of a value of the corresponding type.
A value of the corresponding type is a proof of the proposition.  Thirdly, a
type is interpreted as a logic-programming style rule, i.e., a Prolog rule or
Horn clause~\cite{kowalski}.\footnote{The connection between
type class instances and Prolog rules is folklore.} Resolution~\cite{resolution} connects rules and
propositions: it is the means to show that a proposition is entailed by a set
of rules.
Again, a value
serves as evidence for the rule interpretation, constructing a proof of one
proposition in terms of proofs of others.

%%The interpretation of rules is essential 
%%to retrieve evidence associated with the result of queries.

%if False

To be precise there are 2 query languages involved in our calculus: one
for the type system; and another for the operational semantics. The
role of the query language for the type system is to verify that all
queries are resolvable: if a query is not resolvable, then a
compile-type error should happens. The role of the query language 
for the operational semantics is to retrieve the evidence associated
with a derived fact. For this query language to work, rules (and
consequently types) must be preserved at run-time. This is why our 
operational semantics must include type information.  

\bruno{An alternative presentation of the key design choices}
\subsection*{2.1\quad Motivating the Design of $\ourlang$ (option 2)}

%endif 

This threefold interpretation of types is of course reflected in the
design of our calculus.



\paragraph{Operational semantics carries types} 
In $\ourlang$'s operational semantics, types are interpreted as rules and
determine how queries are answered.  Hence, unlike System F, where static types
do not affect the outcome of computation, $\ourlang$ cannot erase types.

%endif

% or lead to ad-hoc designs of resolution with potential loss of
% expressiveness. 

%}

%-------------------------------------------------------------------------------
\subsection{Operational Semantics}
\label{subsec:opsem}

\figtwocol{fig:opsem}{Operational Semantics}{
\small
\bda{lc} 

\multicolumn{2}{l}{\myruleform{\tstate \turns e \eval v}} \\

\OpQuery &
\myirule
{ \tstate \vturns \rulet \eval v}
{ \tstate \turns ?\rulet \eval v }
\\ \\

\OpRule &
\myirule
{}
{ \tstate \turns \ruleabs{\rulet}{e} \eval 
  \rclos{\rulet, e, \tstate, \shade{\nil}}}
 \\ \\

\OpInst &
\myirule
{ \tstate \turns e \eval 
  \rclos{\rulet', e', \tstate', \shade{\rulepgmvar'}} \\
  \rulet' \leteq \rulesch{\alpha}{\rulesetvar}{\type} 
}
{ \tstate \turns e[\bar{\type}] \eval 
  \subst{\overline{\alpha}}{\overline{\type}}
  \rclos{\rulesetvar \To \type, e', \tstate', \shade{\rulepgmvar'}}
} \\ \\

\OpRApp &
\myirule
{ \tstate \turns e \eval 
  \rclos{\rulet', e', \tstate', \shade{\rulepgmvar'}} \\
  \tstate \turns e_i \eval v_i \quad
  (\forall \relation{e_i}{\rulet_i} \in \rulesetexp) \\
  \tstate'; \rulepgm \shade{\cup~\rulepgmvar'} \turns e' \eval v
}
{ \tstate \turns \ruleapp{e}{\rulesetexp} \eval v
} \\ \\

\multicolumn{2}{l}{\myruleform{\tstate \vturns \rulet \eval v}} \\

\DynRes &
\myirule
{ \lookup{\tstate}{\type} =
  \rclos{\rulesch{\beta}{\pi'}{\type'}, e', 
    \tstate', \shade{\rulepgmvar'}} \\ 
  \rulet \leteq \rulesch{\alpha}{\shade{\pi}}{\type} \quad
  \theta \leteq \unify{\type'}{\type}{\bar{\beta}} \\
  \tstate \vturns \rulet_i \eval v_i \quad 
  (\forall \rulet_i \in \theta \pi' \shade{-~\pi})
}
{ \tstate \vturns \rulet \eval 
  \rclos{\rulet, \theta e', \theta \tstate', 
    \rulepgm \shade{\cup ~ \theta \rulepgmvar'}}
} \\ \\
\eda

\bda{llc}

\multicolumn{1}{l}{\myruleform{\lookup{\tstate}{\type} = v}}
& & \myirule
{
  \lookup{\rulepgmvar}{\type} = v
}
{
  \lookup{(\tstate;\rulepgmvar)}{\type} = v
} \quad

\myirule
{
  \lookup{\rulepgmvar}{\type} = \bot \quad
  \lookup{\tstate}{\type} = v
}
{
  \lookup{(\tstate;\rulepgmvar)}{\type} = v
} \\ \\ 

\multicolumn{1}{l}{\myruleform{\lookup{\rulepgmvar}{\type} = v}} 
& & \myirule
{
  (\rulet:v) \in \rulepgmvar \quad
  \rulet \succ \type \\
  \not \exists (\rulet':v') \in \rulepgmvar. 
  \rulet' \succ \type \wedge (\rulet:v) \neq (\rulet':v'')
}
{
  \lookup{\rulepgmvar}{\type} = v
} \\ \\

& & \myirule
{
  \forall (\rulet:v) \in \rulepgmvar. \rulet \nsucc \type 
}
{
  \lookup{\rulepgmvar}{\type} = \bot
}
\eda
}

The operational semantics, given in Figure \ref{fig:opsem}, is a
call-by-value big-step operational semantics. The judgment $\tstate
\turns e \eval v$ means, as usual, that expression $e$ evaluates to
value $v$ under environment $\tstate$.
{\small
\bda{llrl} 
\text{Values (Closures)} & v \hide{\in \meta{Val}} & ::= &
\rclos{\rulet, e, \tstate, \rulepgmvar} \\
\text{Environments} & \tstate \hide{\in \meta{Env}} & ::= &
\cdot \mid \tstate; \rulepgmvar \\
\text{Rule sets} & \rulepgmvar \hide{\in \meta{Pgm}} & ::= &
\nil \mid \rulepgm \\
\eda 
}
An environment $\tstate$ is a stack of {\it rule sets}. Each rule set
is a set of mappings from rule types to corresponding values. The
stack nature of an environment captures the lexical scope of different
rules.

% In the following example, the
% environment at {\tt (*1*)} is
% $\myset{\relation{\tyint}{1}};\myset{\relation{\tyint}{2}}$:
% \Ex{
%   f = \ruleabs{(\myset{\tyint} \To \tyint)}{(?\tyint)} \\
%   \ruleapp
%   {\ruleapp
%     {f {\tt (* 1 *)} }
%     {\myset{\relation{2}{\tyint}}}}
%   {\myset{\relation{1}{\tyint}}}
% }
% \tom{Fix the above example.}
% The impact of scoping becomes clear when we discuss resolution in section
% \ref{sec:resolution}.

The only values in $\ourlang$ are closures of rule abstractions.
Such a closure $\rclos{\rulet, e, \tstate, \rulepgmvar}$ consists of 
its type $\rulet$, rule body $e$, captured environment $\tstate$ and partially
resolved context $\rulepgmvar$. %%, which is explained shortly.

The operational semantics is syntax-directed. The gray parts of the
operational semantics relate to the partially resolved contexts and can be
ignored for now; we explain
them later.  Rule $\OpRule$ builds a closure from a rule abstraction
in the obvious way.  Rule $\OpInst$ substitutes formal type parameters
by the actually supplied types.  
%Substitution on types, rule types,
%expressions, values, rule programs and environments is formally
%defined in Figure~\ref{fig:subst}. 
Here $\substone$ is a substitution
from type variable $\alpha$ to $\type$ and
$\subst{\bar{\alpha}}{\bar{\type}}$ is a simultaneous substitution of
$[\alpha_1\!\mapsto\!\type_1, \cdots,
\alpha_n\!\mapsto\!\type_n]$.
Finally, rule $\OpRApp$ supplies the
required evidence for the assumptions of a rule closure and evaluates
the rule body to a value.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Resolution}
Rule $\OpQuery$ defines the semantics of queries in terms of auxiliary
judgment $\tstate \vturns \rulet \eval v$, which expresses that rule
type $\rulet$ resolves to $v$ with respect to~$\tstate$.

The underlying principle of (recursive) resolution in $\ourlang$ (and
IP in general) originates from resolution in logic. We assign to each
rule type $\rulet$ a logical interpretation denoted $\rulet^\dagger$:
\begin{eqnarray*}
(\forall \bar{\alpha}.\pi \To \type)^\dagger & = & \forall \bar{\alpha} . \bigwedge_{\rho \in \pi} \rho^\dagger \To \type^\dagger
\end{eqnarray*}
and base types are interpreted as ``there is an implicit value of this type''.
Closures provide the necessary runtime evidence.
% For instance, \textit{rule type} |{Bool} => Int| has logical interpretation $|Bool| \Rightarrow |Int|$.
% In this example, the formula is a Horn clause,\footnote{ ``\texttt{int
% :- bool.}'' in Prolog syntax} but in general implications nest to the left.
Resolution in $\ourlang$ then corresponds to checking entailment of the logical interpretation:
\begin{center}
If $\tstate \vturns \rho \eval v$, then $\tstate^\dagger \models \rho^\dagger$.
\end{center}
Rule $\DynRes$ defines resolution recursively.  First, it looks up a closure
with \textit{matching} rule type (see below for the definition of lookup).
Matching means that the right-hand side $\type'$ of the rule type can be instantiated to
the right-hand side $\type$ of the queried type using a one-way unifier $\theta$.  The
closure type's left-hand side $\theta\pi'$ %, minus the queried LHS $\ruleset$, 
is resolved recursively.  Finally, a ``patched'' form of the closure is returned:
the queried type is provided and the type substitution $\theta$ is applied. 
% and the newly resolved part of the context is added.

%%\bruno{Don't forget to fill in the dots!}
%%This definition of resolution is a \textit{conservative approximation} of
%%logical entailment on several accounts: ...

% Resolution is driven by the interpretation of 
% rule types as first-order logic formulas. This interpretation, denoted $(\cdot)^\dagger$,
% is defined as:
% \begin{eqnarray*}
% (\forall \bar{\alpha}.\pi \To \type)^\dagger & = & \forall \alpha . \bigwedge_{\rho \in \pi} \rho^\dagger \To \type^\dagger \\
% \tstate^\dagger & = & \{ \rho^\dagger \mid (\rho:v) \in \tstate \}
% \end{eqnarray*}
% Resolution conservatively approximates logical entailment:
% \begin{theorem}
% If $\tstate \vturns \rho \eval v$, then $\tstate^\dagger \models \rho^\dagger$.
% \end{theorem}
% The opposite does not hold for two reasons. Firstly, and most importantly, the
% value-level evidence of rule closures only supports left-to-right reasoning.
% Secondly, we restrict the power of recursive resolution to simplify reasoning
% about program behavior and properties. The logical interpretation of the recursive precondition
% of rule $\DynRes$ is:
% \[ \forall \rho^\dagger \in \theta\pi'^\dagger. \rho^\dagger \in \pi^\dagger \vee \tstate^\dagger \models \rho^\dagger \]
% which is stronger than the necessary condition:
% \[ \forall \rho^\dagger \in \theta\pi'^\dagger. \tstate^\dagger \wedge \pi^\dagger \models \rho^\dagger \]
% We return to the reason for this stronger condition \tom{later} when we investigate resolution in detail.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Lookup}

% During dynamic query resolution, environment may have multiple rules match
% with given query. With in an environment, rules in a context nearest to the
% environment stack top is preferred. With in a context, we don't allow multiple
% matches. 

Figure \ref{fig:opsem} defines lookup of a type in environments
($\lookup{\tstate}{\type}$) and rule sets
($\lookup{\rulepgmvar}{\type}$).  Lookup in a rule set only yields a
result when it contains \textit{at most} one matching rule: it yields
the rule closure,\footnote{as in Prolog, quantified type variables should be renamed apart to
avoid variable capture}
if there is exactly one matching rule, and $\bot$ if
there is no matching rule.  Lookup in an environment, first looks in
the topmost rule set, and, in case of $\bot$, recursively looks in the
remainder of the environment.  

If a rule set contains multiple matching rules (overlapping rules),
the lookup is not defined.  Here,
$(\forall \bar{\alpha}.\pi \To
  \type') \succ \type \stackrel{\mathit{def}}{=} \exists \theta. \theta
  = \unify{\type'}{\type}{\bar{\alpha}}$,
where $\unify{\type'}{\type}{\bar{\alpha}}$ returns the most general
unifier of $\type'$ and $\type$ with its support set contained in
$\bar{\alpha}$.  Note that overlapping rules, which are allowed in
Haskell, can be modeled in $\ourlang$ using nested scoping, even
though they are not supported directly (see Section 5).



%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Partially Resolved Contexts}
The partially resolved context $\rulepgmvar$ in the operational semantics
provides extra expressivity to deal with higher-order queries, i.e., $\tstate
\vturns \forall \bar{\alpha}.\pi \To \type \eval v$ where $\pi$ is non-empty.

Rule $\DynRes$ does not require an exact syntactic match $\unify{\pi'
  \To \type'}{\pi \To \type}{\bar{\beta}}$ between the queried
higher-order rule type and the one found in the environment. Instead,
there can be some remainder $\theta\pi' - \pi$ of the found rule,
which the query does not demand to be resolved right away. Hence, we
say that the found rule is \textit{partially resolved}. The evidence
for this partially resolved context is stored in the rule closure's
fourth component.

The partially resolved context is treated as follows: It starts out as
empty when a new closure is created in rule $\OpRule$. Then
(potentially multiple successive) applications of rule $\DynRes$ may
extend it: the part of the context that is not required by a
higher-order query is resolved and stored in the closure.  Finally,
rule $\OpRApp$ supplies the remainder of the context, adds it to the
front of the environment and evaluates the rule body. A non-empty
partially resolved context arises, for instance in the following
program:

> let f = rule ({Int, Bool} => Int) e in 
>   (rule (rulet) (?({Int} => Int)) with 
>     { f : {Int, Bool} => Int, True : Bool })

where | rulet = {{Int, Bool} => Int, Bool} => ({Int} => Int)|.
The resulting closure has the form 
$\rclos{|{Int} => Int, e, -, {Bool : True}|}$.

% \begin{equation*}
% \myirule
% { \env(\type) = \ruleset' \To \type \\
%   \env, \ruleset \vturns \rulet_i' \quad
%   (\forall \rulet_i' \in \ruleset')
% }
% { \env \vturns \ruleset \To \type}
% \end{equation*}
% The recursive instance of this rule is more powerful.
% However, this more powerful rule extends the implicit environment. \ldots


% [TOM] This discussion belongs elsewhere. It is not about partial resolution
%       in particular, but resolution in general. Moreover, it concerns 
%       a surprising behavior that could be ruled out by the type system.
%       So I think it is more appropriate in the type system section.
%
% During partial resolution, subqueries may include uninstantiated type 
% variables. Their instantiation will be determined in future. 
% But until
% then, it will be safe to consider that they can be anything.
% Consider following example.
% \[\begin{array}{l}
%   \{ \forall a. a \rightarrow \tybool,\ 
%      \tyint \rightarrow \tybool,\ 
%      \forall a. \{a \rightarrow \tybool, a\times a\} \Rightarrow a\} \\
%   \turns (?\forall a.\{a \times a\}\Rightarrow a)[\tyint]
% \end{array}\]
% During the evaluation of the query part, the third rule will be taken at first.
% Then, to resolve difference between the query and the taken rule, 
% evaluation process have to resolve query $a \rightarrow \tybool$ type. 
% Since, we don't have enough type information, it will be safe to pick
% $\forall a.\rightarrow a \rightarrow \tybool$. 
% 
% Alternative is to detect cases where type information can be uncertain even
% at runtime and reject programs having such possibility using type system. 

% \wc{Figure on substitutions is moved to appendix}
% \tom{Where is it? I don't see it in the appendix}

\paragraph{Resolution Design}
Note that rule~$\DynRes$ is not as strong as it could be when purely
considering the logical interpretation of rules. In terms of proposition logic,
it does not allow to prove $A \rightarrow B$ from $A \rightarrow C$ and $C
\rightarrow B$. It only proves $A \rightarrow B$ from, e.g.,
$C \rightarrow B$ and $C$.
To obtain stronger resolution,  we would have to add $\pi$ as
a set of available assumptions to the environment:
\[ \myirule
{ \lookup{\tstate}{\type} = 
  \rclos{\rulesch{\beta}{\pi'}{\type'}, e', 
    \tstate', \rulepgmvar'} \\ 
  \rulet \leteq \rulesch{\alpha}{\pi}{\type} \quad
  \theta \leteq \unify{\type'}{\type}{\bar{\beta}} \\
  \tstate\shade{;\pi:\Box} \vturns \rulet_i \eval v_i \quad 
  (\forall \rulet_i \in \theta \pi')
}
{ \tstate \vturns \rulet \eval 
  \rclos{\rulet, \theta e', \theta \tstate', 
    \rulepgm \cup  \theta \rulepgmvar'}
} \]
However, there are two practical problems with that. Firstly, we do not have
any value-level evidence ($\Box$) for $\pi$ yet. Secondly and most importantly,
in this variant a query involves not one single environment
throughout, but many: a new one in every recursive resolution step.  This makes it
much harder to reason about safety and coherence properties, both for the
programmer and for an automatic type checker. For these two reasons, we have
decided to adopt the simpler resolution rule.
%-------------------------------------------------------------------------------
\subsection{Runtime Errors and Coherence Failures}
\label{subsec:error}
In $\ourlang$, ill-behaved programs either raise runtime errors or are
incoherent. The principal source of runtime errors is query failure,
which is caused by either lookup failure or ambiguous instantiation
during resolution. Coherence failure happens when a query in a
program does not have a single nearest match or its single nearest
match is not the one used at runtime.

\paragraph{Lookup Failures}
A lookup fails if there is no matching rule in the rule environment,
or there are multiple matching rules.

The first cause, no matching rule, is the simplest, illustrated by the
following two examples:
\[\begin{array}{rl}
\myset{} &\turns  |query Int| \\
\myset{|{Bool} => Int : -|}& \turns |query Int|
\end{array}
\noindent \]
In the first example, resolution does not find a matching rule for the
given |Int| type in the environment. In the second example,
resolution finds a matching rule for |Int| in the first step, but
does not find one in the recursive step for |Bool|.

The second cause are multiple matching rules, which is the case in the
following two examples:

> {Int : 1, Int : 2} turns (query Int)
> {forall a.a -> Int : -, forall a.Int -> a : - } turns (query (Int -> Int))
\noindent

In the first example, two different rules produce a value for the same
type |Int|; arbitrarily choosing one of 1 and 2
makes the program's behavior unpredictable. To avoid this ambiguity,
the lookup fails instead. The second example shows that two rules can
be used to produce a value of the same type, even though the rule
types are different. The two polymorphic rule types can be instantiated to the
same type, in this case to |Int -> Int|.

\paragraph{Ambiguous Instantiations}
In some cases, resolution does not determine how to instantiate a
fetched rule. Consider the following example:\footnote{$\rclos{n}$
  denotes a closure value; distinct numbers mean distinct values.}\[
\begin{array}{rl}
  \myset{\quad 
    |forall a.{a -> a} => Int : rclos 1| &, \\
    |Bool -> Bool : rclos 2|&, \\
    |forall b. b -> b : rclos 3|&} \turns |query Int|
\end{array}\]
% > { forall a. {a -> a} => Int : (rclos 1), Int -> Int : (rclos 2),
% >  Bool -> Bool : (rclos 3) } turns (query Int)
The |query Int| matches the first rule without determining an
instantiation for |a|. However, the runtime behavior could actually
depend on the choice between |rclos 2| and |rclos 3|. Thus the query
is ambiguous.

\paragraph{Coherence Failures}
A program is coherent iff every query in the program has a single,
lexically nearest match, which is the same statically and at runtime. This
means that all the runtime queries instantiated from the original
query should have the same resolution result. Consider the following
example:

> let f : forall b.b -> b =
>   implicit {fun (x) (x) : forall a. a -> a} in
>       query (b -> b)
\noindent
This program is coherent because no matter which type the type
variable |b| will have at runtime, the resolution results for all
those queries are the same (|forall a. a -> a|). However, the following program is
incoherent:

> let f : forall b.b -> b =
>   implicit {fun (x) (x) : forall a. a -> a} in
>      implicit {fun (n) (n + 1) : Int -> Int} in 
>       query (b -> b)
\noindent
There are two possible results for the query |query (b -> b)|
depending on the type of |b| at runtime. If the query is instantiated
by the substitution $\subst{|b|}{|Int|}$, then the nearest result is
|Int -> Int| and otherwise, |forall a. a -> a| is the one.

Our static type system will safely reject such programs that can have
the aforementioned runtime errors or coherence failures.

%%% Local Variables: 
%%% mode: latex
%%% TeX-master: "../Main"
%%% End: 

%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Rule.fmt

%format === = "\cong"

\section{Overview}
\label{sec:overview}

This section presents relevant background on type classes, IP 
and coherence, and it introduces the key features of our calculus for ensuring coherence.

\subsection{Type Classes and Implicit Programming}

\subsection{Coherence in Type Classes}

A programming language is said to be coherent if
any valid program has exactly one meaning (that is,
the semantics is not ambiguous). Haskell type classes preserve
coherence, but not for free. Since the first implementations of type
classes, Haskell imposes several restrictions to guarantee
coherence. For example, the expression:

> show (read ''3'') == ''3'' 

\noindent where functions |show| and |read| have the types: 

> show :: Show a => a -> String
> read :: Read a => String -> a

\noindent is rejected in Haskell due to \emph{ambiguity} of 
\emph{type class resolution}~\cite{jones}. The functions |show| and
|read| respectively print and parse values of a certain type |a|. 
The type |a| can be any type that implements the classes |Show| 
and |Read|. For example, it could be |Int|, |Float| or |Char|. The
reason for rejecting the program is precisely that multiple choices 
exists for instantiating the type |a|. Depending on such choice, the 
semantics of the expression could be different. For example, chosing 
|a=Float| leads to |False|, since showing the float 3 would result 
in the ``3.0''. In contrast chosing |a=Int| leads to |True|, since the
string is the same.

\paragraph{Overlapping and Incoherent Instances} 
Advanced features of type classes, such as overlapping
instances~\cite{}, pose even more severe problems. In purely
functional programming, ``\emph{substituting equals by equals}'' is
expected to hold. That is, when given two equivalent expressions then
replacing one by the other in \emph{any context} will always lead to
two programs that yield the same result. Special care (via
restrictions) is needed to preserve coherence and the ability of
substituting equals by equals in the presence of overlapping
instances. The following program illustrates the issues:

> class Trans a where trans :: a -> a
>
> instance Trans a where trans x = x
>
> instance Trans Int where trans x = x+1
>
> bad :: a -> a
> bad x = trans x  -- incoherent definition!

Consider the following reasoning steps:

> bad 1
> = {- definition of |bad| -}
> trans 1
> = {- definition of |trans| -}
> 1+1
> = {- arithmetic -}
> 2

< bad :: a -> a

\subsection{Our Calculus}

Our calculus $\ourlang$ combines standard scoping mechanisms 
(abstractions and applications) and types \`a la System F, with a
logic-programming-style query language. 
At the heart of the language is a threefold interpretation of types:
\begin{center}
  |types === propositions === rules|
\end{center}
\noindent Firstly, types have their traditional meaning of classifying
terms.  Secondly, via the Curry-Howard isomorphism, types can
also be interpreted as propositions -- in the context of GP, the type
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

Next we present the key features of $\ourlang$ and how
these features are used for GP. For readability purposes we sometimes omit
redundant type annotations and slightly simplify the syntax. 

\paragraph{Fetching values by types} A central construct in
$\ourlang$ is a query. Queries allow values to be fetched by type, not by name.  
  For example, in the following function call

< foo (query Int)
 
the query |query Int| looks up a value of type |Int| in the implicit
environment, to serve as an actual argument.


%%Function \texttt{inc} is applied to an argument (we call ``implicit
%%query'') that queries ``$\qask{\tyInt}$'' by mentioning just its
%%type \tyInt.  The int-typed entry in the current implicit
%%environment is looked up  to provide an integer value. 

%%In practice, the implicit query ``$\qask{\tyInt}$'' can even be
%%omitted thanks to type inference. Our calculus makes implicit queries
%%always manifest in text. 

\paragraph{Constructing values with type-directed rules} $\ourlang$ constructs values, using
programmer-defined, type-directed rules (similar to functions). A rule (or rule
abstraction) defines how to compute, from implicit arguments, a value of a
particular type. For example, here is a rule that given an implicit |Int| value, 
adds one to that value:

< rule Int ((query Int) + 1)

\noindent The rule abstraction syntax resembles a traditional $\lambda$ expression. 
However, instead of having a variable as argument, a rule abstraction ($\lambda_?$)
has a type as argument. The type argument denotes the availability of a value 
of that type (in this case |Int|) in the implicit environment inside the body 
of the rule abstraction. Thus, queries over the rule abstraction type argument
inside the rule body will succeed. 

The type of the rule above is:

< Int => Int

\noindent This type denotes that the rule has type |Int| provided the 
availability of a value of type |Int| in the implicit environment. 
The implicit environment is extended through rule application (analogous to
extending the environment with function applications).
Rule application is expressed as, for example:

< (rule Int ((query Int) + 1)) with 1

With syntactic sugar similar to a |let|-expression, a rule abstraction-application 
combination is more compactly denoted as:
%%\[
%%\qlet{\{\texttt{1},\texttt{true}\}}
%%     {\texttt{(\qask{\tyInt}+1, not\;\qask{\tyBool})}}
%%\]


%% \noindent which can be used 

< implicit 1 in ((query Int) + 1)

\noindent Both expressions return |2|. 

\paragraph{Rule Currying} 
Like traditional lambdas, rule abstractions can be curried.
Here is a rule that computes an |Pair Int Bool| 
pair from implicit |Int| and |Bool| values:

%%\[
%%\qlam{\tyInt, \tyBool}
%%     {\texttt{(\qask{\tyInt}+1, not\;\qask{\tyBool})}}.
%%\]

< rule Int (rule Bool (((query Int) + 1, not (query Bool))))

In the body of the second rule abstraction, two implicit values (of type
|Int| and |Bool| respectively) are available in the implicit environment.
The type of this rule is :

< Int => Bool => Pair Int Bool

\noindent Using two rule applications it is possible to provide the implicit 
values to the two rule abstractions. For example:

\begin{comment}
The rule abstraction syntax resembles a type-annotated expression: the
expression |((query Int) + 1, not (query Bool))|
to the left of the colon is
the \emph{rule body}, and to the right is the \emph{rule type} |{Int, Bool} =>
Pair Int Bool|. A rule abstraction abstracts over a set of implicit
values (here |{Int,Bool}|), or, more generally, over rules to build 
values. 

< rule ({Int, Bool} => Pair Int Bool) (((query Int) + 1, not (query Bool)))

%% are \emph{bound} to the rule body.  In
%%$\ourlang$ static types also play the roles of variables in rule
%%abstractions.

%%We write the above rule's type as
%%$\rulety{\tyInt,\tyBool}{\tyInt\times\tyBool}$. 

Hence, when a value of type |Pair Int Bool| is needed (expressed by the query |query
(Pair Int Bool)|), the above rule can be used, provided that an integer and
a boolean value are available in the implicit environment. In such an
environment, the rule returns a pair of the incremented |Int| value and negated
|Bool| value.

The implicit environment is extended through rule application (analogous to
extending the environment with function applications).
Rule application is expressed as, for example:
%\[
%\qapp{\qlam{\tyInt, \tyBool}
%      {\texttt{(\qask{\tyInt}+1, not\;\qask{\tyBool})}}
%     }{\{\texttt{1},\texttt{true}\}}.
%\]

< rule ({Int, Bool} => Pair Int Bool) (((query Int) + 1, not (query Bool))) 
<    with {1,True}

With syntactic sugar similar to a |let|-expression, a rule abstraction-application 
combination is denoted more compactly as:
%%\[
%%\qlet{\{\texttt{1},\texttt{true}\}}
%%     {\texttt{(\qask{\tyInt}+1, not\;\qask{\tyBool})}}
%%\]


%% \noindent which can be used 

< implicit {1,True} in ((query Int) + 1, not (query Bool))

\end{comment}

< implicit 1 in
<  implicit True in 
<    ((query Int) + 1, not (query Bool))

\noindent which returns |(2,False)|. 

\paragraph{Higher-order rules} $\ourlang$ supports higher-order
rules. For example, the rule 
%%\[
%%\qlam{\tyInt,\rulety{\tyInt}{\tyInt\times\tyInt}}{\qask{(\tyInt\times\tyInt)}}
%%\]

> rule Int (rule ((Int => Pair Int Int)) (query (Pair Int Int)))

when applied, will compute an integer pair given an integer and a rule to
compute an integer pair from an integer. This rule is higher-order because 
another rule (of type |Int => Pair Int Int|) is used as an argument.
The following expression returns $(3, 4)$:
%%\[
%%\qlet{\{\texttt{3},\qlam{\tyInt}{\texttt{(\qask{\tyInt},\qask{\tyInt}+1)}}\}}
%%     {\qask{(\tyInt\times\tyInt)}}.
%%\]

< implicit 3 in 
<  implicit (rule Int (((query Int), (query Int) + 1))) in 
<    query (Pair Int Int)

\paragraph{Recursive resolution} 
Note that resolving the  query |(query (Pair Int Int))| above
involves applying multiple rules. 
%combining multiple rules. 
The current environment does not contain
the required integer pair. It does however contain the integer $3$ and a rule 
%$\qlam{\tyInt}{\texttt{(\qask{\tyInt},\qask{\tyInt}+1)}}$
|rule (Int => Pair Int Int) (((query Int), (query Int) + 1))| to compute a
pair from an integer. Hence, the query is resolved with $(3,4)$, the
result of applying the pair-producing rule to $3$.

\paragraph{Polymorphic rules and queries} $\ourlang$ allows polymorphic rules. For example, the rule 
%%\[
%%\qLam{\alpha}{\qlam{\alpha}{(\qask{\alpha},\qask{\alpha})}},
%%\]

%format biglam a n = "\Lambda " a ". " n 

< biglam a (rule a (((query a),(query a))))

\noindent abstracts over a type using standard type abstraction and then uses 
a rule abstraction to provide a value of type |a| in the implicit environment of 
the rule body. This rule has type

< forall a . a => Pair a a

and can be instantiated to multiple rules of monomorphic types
%%\[
%%\rulety{\tyint}{\tyint\times\tyint}, 
%%\rulety{\tybool}{\tybool\times\tybool}, \cdots.
%%\]

%format dots = "\ldots"

< Int => Pair Int Int, Bool => Pair Bool Bool, dots

Multiple monomorphic queries can be resolved by the same
rule. The following expression returns 
|((3,3),(True,True))|: 

%if False

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

%endif

> implicit 3 in
>   implicit True in 
>     implicit (biglam a (rule a (((query a),(query a))))) in
>       (query (Pair Int Int), query (Pair Bool Bool))

Polymorphic rules can also be used to resolve polymorphic queries:

> implicit (biglam a (rule a (((query a),(query a))))) in
>   (query (forall a . a => Pair a a))

\paragraph{Combining higher-order and polymorphic rules} 
The rule 
%if False
\[
\qlam{\tyInt,\forall\alpha.\rulety{\alpha}{\alpha\times\alpha}}
 {\qask{((\tyInt\times\tyInt)\times(\tyInt\times\tyInt))}}
\]
%endif

> rule Int (rule ((forall a . a => Pair a a)) (((query (Pair (Pair Int Int) (Pair Int Int)))))) 

prescribes how to build a pair of integer pairs, inductively from an
integer value, by consecutively applying the rule of type
%if False
\[
\forall\alpha.\rulety{\alpha}{\alpha\times\alpha}
\]
%endif

< forall a . a => Pair a a

twice: first to an integer, and again to the result (an
integer pair). For example, the following expression returns $((3,3),(3,3))$:

%if False
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
%endif 

> implicit 3 in
>  implicit (biglam a (rule a (((query a),(query a))))) in
>    (query (Pair (Pair Int Int) (Pair Int Int)))

%%rule (forall a . {a} => Pair a a) (((query a),(query a)))} in


% The $(3,3)$ pair is from applying the rule 
% %% $\qLam{\alpha}{\qlam{\alpha}{(\qask{\alpha},\qask{\alpha})}}$
% |rule (forall a . {a} => Pair a a) (((query a),(query a)))|
% to $3$, and the final answer $((3,3),(3,3))$ from applying the same
% rule to $(3,3)$.

\paragraph{Locally and lexically scoped rules} 
Rules can be nested and resolution respects the lexical scope of rules. 
Consider the following program: 

> implicit 1 in 
>   implicit True in
>     implicit (rule Bool (if (query Bool) then 2 else 0)) in
>       query Int

The query $\qask{\tyint}$ is not resolved with the
integer value |1|. Instead the rule that returns an integer from a boolean
is applied to the boolean |True|, because that rule
can provide an integer value and it is nearer to the query. So, 
the program returns $2$ and not $1$.

%if False

Suppose the rule 

\[
\qlam{\tyInt}
 {\qlam{\tyBool, \rulety{\tyBool}{\tyInt}}
       {\qask{\tyInt}}
 }
\]


> rule ({Int} => {Bool, {Bool} => Int} => Int) ((query Int)) 

is applied to an integer, and then to a boolean and a rule of type 
|{Bool} => Int|. Resolving the query |(query Int)|
always selects the lexically nearest abstraction.

That is, the query $\qask{\tyint}$ is not resolved with the
integer value, but by applying boolean value the
rule that returns an integer from a boolean. So, the following example
returns $2$ and not $1$:

\[
\begin{array}{l}
\texttt{implicit}\;\{\texttt{1}\}\;\texttt{in}\\
\mbox{\ \ \ }\texttt{implicit}\;\{\texttt{true},\;
\qlam{\tyBool}{\texttt{if}\;\qask{\tyBool}\;\texttt{then 2}}\}\;\texttt{in}\\
\mbox{\ \ \ \ \ \ }\qask{\tyInt}.
\end{array}
\]
%endif



\paragraph{Overlapping rules} 
Two rules overlap if their return types intersect, i.e., when they can both 
be used to resolve the same query. Overlapping rules are
allowed in $\ourlang$ through nested scoping. The nearest matching
rule takes priority over other matching rules. For example consider 
the following program:

%if False

A program is coherent iff every query in it has a single, lexically
nearest match and this nearest match is the one actually used for the
query at runtime. The following program is coherent:

%endif

> implicit (biglam a (fun (x) (x))) in 
>    implicit (fun (n) (n + 1)) in 
>       query (Int -> Int) 1

In this case |fun (n) (n + 1)| (of type |Int -> Int|) is the lexically nearest
match in the implicit environment and evaluating this program results 
in |2|. However, if we have the following program instead:

> implicit (fun (n) (n + 1)) in 
>   implicit (biglam a (fun (x) (x))) in  
>      query (Int -> Int) 1

Then the lexically nearest match is |biglam a (fun (x) (x))| (of type |forall a. a  -> a|)
and evaluating this program results in |1|.

\paragraph{Overlapping rules and coherence:} 
A program is coherent iff every query in it has a single, lexically nearest
match. It is
well-known~\cite{designspace} that coherence cannot always be guaranteed in the
presence of overlapping rules. Consider for instance the program:

> let f : forall b.b -> b =
>   implicit (fun (x) (x) : forall a. a -> a) in
>      implicit (fun (n) (n + 1) : Int -> Int) in 
>       query (b -> b)
> in f Int 1

While the query |query (b -> b)| always matches |forall a. a -> a|, that is not
always the lexically nearest match. Indeed, in case |b| is instantiated to
|Int| the rule |Int -> Int| is a nearer match. However, in case |b| is
instantiated to any other type, |Int -> Int| is not a valid match. In summary,
we cannot in all cases statically determine the lexically nearest match. 

One might consider to resolve the incoherence by picking the lexically nearest
rule that matches all possible instantiations of the query, e.g., |forall
a. a -> a| in the example. In the case of overlapping type family instances for Haskell~\cite{eisenberg},
that approach leads to type unsoundness. There is not such threat here, nor is
there for overlapping type class instances in Haskell~\cite{???}. Nevertheless, allowing
this form of incoherence is undesirable for two reasons. Firstly, because it
makes the behavior of programs harder to predict, and, secondly, because
the behavior of programs is not stable under inlining.
For these reasons we reject incoherent programs.

%if False

Overlapping rules pose a well-known challenge~\cite{designspace}: in
certain programs the presence of overlapping rules fails the coherence
condition because there can be no single nearest match. Such incoherent
programs are undesirable as they are hard to understand and reason
about. Therefore incoherent programs like the following are rejected:

> let f : forall b.b -> b =
>   implicit {fun (x) (x) : forall a. a -> a} in
>      implicit {fun (n) (n + 1) : Int -> Int} in 
>       query (b -> b)
> in f<#Int#> 1

Note that in f's definition, its query |query (b -> b)| does not have
a single match. Neither |forall a. a -> a| nor |Int -> Int| can be
selected. Even if we selected |forall a. a -> a|, as it will work for
all possible instantiations of |b|, this selection is incoherent when
|b| is instantiated to |Int|, because in that case the nearest
match would be |fun (n) (n + 1) : Int -> Int|.

%endif

%% Finally not that while $\ourlang$ does not allow overlapping with 

%if False

Two rules overlap if their return types intersect, i.e, when they can both 
be used to resolve the same query.
In certain programs, 
the presence of overlapping rules makes naive and apparently correct transformations 
incorrect. This is clearly undesirable and such programs should be rejected.
%Such ambiguity is clearly undesirable, and ambiguous programs should be rejected.
% to ensure that the behaviour of programs is consistently predictable.  

$\ourlang$ adopts the following \emph{coherence} principle: the statically
matched rule must always be the most specific one. Under this principle the
following program is rejected:

%if False

The \emph{coherence} principle states under what conditions the behavior of
resolution is consistently predictable in the presence of
overlapping rules. $\ourlang$ adopts this principle and rejects
programs like the following one:

%endif

> let f : forall b.b -> b =
>   implicit {fun (x) (x) : forall a. a -> a} in 
>     implicit {fun (n) (n + 1) : Int -> Int} in 
>       query (b -> b)
> in f<#Int#> 1

because in |f| the only rule that can be selected for all possible 
instantiations of |b| is |fun (x) (x) : forall a. a -> a|, but when 
|b| is instantiated to |Int| the nearest matching would be |fun (n) (n + 1) : Int -> Int|.

If we did accept this program, evaluating | f<#Int#> 1| would result in |1|. However, 
inlining the definition of |f| at its call site, while in the process 
instantiating |b| to |Int| (an apparently correct transformation) 
leads to the following (valid, but different) program, which results in |2|:

> implicit {fun (x) (x) : forall a. a -> a} in 
>    implicit {fun (n) (n + 1) : Int -> Int} in 
>       query (Int -> Int) 1

%endif

%% In essence the coherence principle states that the nearest matching rule 
%% must always be picked. In the first program this principle is violated (when |b| is |Int|), 
%% whereas in the second it is not.

%if False

 Two rules overlap if their 
return types intersect, hence they can both be used to resolve the same 
implicit query. In the presence of polymorphism, overlapping leads to tricky 
situations. Consider the following example:



The definition of $f$ uses two nested scopes to introduce two
overlapping values in the implicit environment. However, it 
is not obvious which value to use to resolve the query |(query (b -> b)|. 
When |b| is instantiated to |Int| the natural choice is, to pick |fun (n) (n + 1) : Int -> Int|, 
but for any other instantiation of |b| the only possible choice is 
|fun (x) (x) : forall a. a -> a|. If we make the latter choice, which is always 
type-safe, then | f<#Int#> 1| evaluates to |1|. However, naive and
apparently correct transformation can change the semantics of the program. 
For example, by inlining the definition of |f| at its call site, while in the process 
changing instantiating |b| to |Int| leads to a program that evaluates to |2|. 

Both values 
can be used to resolve the query | (query (Int -> Int)| 


According to the coherence principle, resolving the 
implicit query $\qask{\beta\to\beta}$ is determined at $f$'s
instantiations: the first $f$ must be $\lambda
n.n+1$ and the second $f$ must be $\lambda x.x$. 

Here, both 

  The coherence principle states under what conditions the behavior of
  resolution is consistently predictable in the presence of
  overlapping rules. Without coherence, programming with implicit
  values is a tricky business, fragile and unpredictable.

  The coherence: the most concrete resolution rule is
  always chosen modulo the lexical scoping. For example, consider the
  following code: 
%if False
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
%endif

> let f : forall b.b -> b =
>   implicit {fun (x) (x) : forall a. a -> a} in 
>     implicit {fun (n) (n + 1) : Int -> Int} in 
>       query (b -> b)
> in (f<#Int#> 1, f<#Bool#> True)

\tom{the above example violates parametricity, see discussion in types section}

The definition of $f$ uses two nested scopes to introduce two
overlapping values in the implicit environment.
According to the coherence principle, resolving the 
implicit query $\qask{\beta\to\beta}$ is determined at $f$'s
instantiations: the first $f$ must be $\lambda
n.n+1$ and the second $f$ must be $\lambda x.x$. 
%% \end{itemize}

%This \emph{resolution} mechanism to automatically infer
%function arguments based on available type information.  User-supplied
%\emph{rules} determine which values resolution infers. 

%endif

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

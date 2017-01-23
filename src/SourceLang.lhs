%include lhs2TeX.fmt
%include polycode.fmt
%include Scala.fmt
%include forall.fmt
%include Rule.fmt

%format record = "{\bf interface}"
%format # = "."
%format dots = "\dots"

\section{Source Languages and Implicit Instantiation}
\label{sec:example}
Languages like Haskell and Scala provide a lot more programmer convenience than
$\ourlang$ (which is a low level core language) because of
higher-level GP constructs, interfaces and implicit instantiation.
This section illustrates how to build a simple source language
on top
of $\ourlang$
to add the expected convenience. 
We should note that unlike Haskell this language
supports local and nested scoping, and unlike both Haskell and Scala 
it supports higher-order rules. We present the type-directed 
translation from the source to $\ourlang$. 

%%< record Eq a = {eqImpl : a -> a -> Bool}
%%<
%%< let  (==) : forall a . {Eq a} => a -> a -> Bool = eqImpl ? in
%%< let  eqInt : Eq Int   = Eq {eqImpl = primEqInt} in
%%< let  eqInt2 : Eq Int = Eq {eqImpl = \x y # isEven x && isEven y} in
%%< let  eqBool : Eq Bool = Eq {eqImpl = primEqBool} in
%%< let  eqPair : forall a b . {Eq a, Eq b} => Eq (a,b)  = 
%%<       Eq {eqImpl = \x y #  fst x == fst y && snd x == snd y} in
%%< let p1 : (Int,Bool) = (4,True) in
%%< let p2 : (Int, Bool) = (8,True) in
%%< implicit {eqInt, eqBool, eqPair} in
%%< 
%%< (p1 == p2, implicit {eqInt2} in p1 == p2) 


\subsection{Type-directed Translation to $\ourlang$}
\label{subsec:trans_src}

%format p1 = "\Varid{p}_1"
%format p2 = "\Varid{p}_2"
%format eqInt = "\Varid{eqInt_1}"
%format eqInt2 = "\Varid{eqInt_2}"
%format eqImpl = "\Varid{eq}"

\begin{figure}
\small

< class Eq a where 
<    (==) : a -> a -> Bool;
<
< instance Eq Int where
<    (==) = primEqInt;
<
< instance Eq Bool where 
<    (==) = primEqBool;
<
< instance (Eq a, Eq b) => Eq (a,b)  where 
<    (==) = \x y #  fst x == fst y && snd x == snd y;
<
< let p1 : (Int,Bool) = (4,True) in
< let p2 : (Int, Bool) = (8,True) in
< 
< (p1 == p2, 
< instance Eq Int where
<    (==) = \x y # isEven x && isEven y;
<
< p1 == p2) 

\caption{Simple Equality Type Class with Anonymous Instances}

\label{fig:eq}

\end{figure}

\begin{figure}
\small

< class Eq a where 
<    (==) : a -> a -> Bool;
<
< instance eqInt2@Eq Int where
<    (==) = \x y # isEven x && isEven y;
<
< instance eqInt@Eq Int where
<    (==) = primEqInt;
<
< instance eqBool@Eq Bool where 
<    (==) = primEqBool;
<
< instance eqPair@(Eq a, Eq b) => Eq (a,b)  where 
<    (==) = \x y #  fst x == fst y && snd x == snd y;
<
< let p1 : (Int,Bool) = (4,True) in
< let p2 : (Int, Bool) = (8,True) in
< 
< (p1 == p2, implicit eqInt2 in p1 == p2) 

\caption{Simple Equality Type Class with Named Instances}

\label{fig:eq}

\end{figure}

\begin{figure}
\small

< class Eq a where 
<    (==) : a -> a -> Bool;
<
< instance Eq Int where
<    (==) = primEqInt;
<
< instance Eq Bool where 
<    (==) = primEqBool;
<
< instance (Eq a, Eq b) => Eq (a,b)  where 
<    (==) = \x y #  fst x == fst y && snd x == snd y;
<
< let p1 : (Int,Bool) = (4,True) in
< let p2 : (Int, Bool) = (8,True) in
<
< let eqInt2 : Eq Int = Eq {(==) = \x y # isEven x && isEven y} in
< 
< (p1 == p2, implicit eqInt2 in p1 == p2) 

\caption{Simple Equality Type Class with Non-Implicit Instances}

\label{fig:eq}

\end{figure}

\newcommand{\typeSrc}{T}
\newcommand{\envSrc}{G}
\figtwocol{f:syntax}{Syntax of Source Language}{
\small
\bda{l}

%\ba{l}
%\textbf{Interface Declarations} \\
%\quad \textbf{interface}~I~\bar{\alpha}~=~\overline{\relation{u}{T}}
%\ea 
%\\ \\

\ba{lrll}
\multicolumn{3}{l}{\textbf{Types}} \\
\typeSrc & ::=  & \alpha             & \mbox{Type Variables} \\
%%      & \mid & \tyint                & \mbox{Integer Type} \\
      & \mid & C~\bar{\typeSrc}       & \mbox{Class Type} \\
      & \mid & \typeSrc \to \typeSrc    & \mbox{Function} \\

\sigma & ::=  & \forall \overline{\alpha}.~\overline{\sigma} \To \typeSrc & \mbox{Rule Type} \\

\ea 
\\ \\

\ba{lrll}
\multicolumn{3}{l}{\textbf{Declarations}} \\
D & ::= & C_D; D \mid E : T & \mbox{Declarations} \\

C_D  & ::= & {\bf class}~C~\bar{\alpha}~{\bf
    where}~\overline{\relation{u}{T}} &\mbox{Class Declaration}
\ea
\\ \\

\ba{lrll}
\multicolumn{3}{l}{\textbf{Expressions}} \\
E & ::= & x & \mbox{Lambda Variable} \\
%%  & \mid & \relation{E}{\typeSrc} & \mbox{Type Annotation} \\
  & \mid & \abs{x}{E} & \mbox{Abstraction} \\
  & \mid & E_1~E_2 & \mbox{Application} \\
  & \mid & u & \mbox{Let Variable} \\
  & \mid & {\bf let~} u~$: $ \sigma ~=~ E_1 {\bf~in~} E_2 & \mbox{Let}\\
  & \mid & {\bf implicit~} \overline{u} {\bf~in~} E_2 & \mbox{Implicit Scoping} \\
%%& n & \mbox{Integer Literal} \\
%%  & \mid & u {\bf~with~} \overline{u} & \mbox{Explicit Overriding} \\
%%  & \mid & ? & \mbox{Implicit Lookup} \\
%%  & \mid & {\bf class}~C~\bar{\alpha}~{\bf
%%    where}~\overline{\relation{u}{T}};~E &\mbox{Class Declaration}\\
  & \mid & C~\overline{u = E} & \mbox{Class Instance}
\ea

\eda
}

\newcommand{\sem}[1]{\llbracket#1\rrbracket}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Translation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\figtwocol{f:type}{Type-directed Encoding of Source Language in $\ourlang$}{
\small
\bda{llrl} 
\text{Type Environments} & \envSrc & ::= & \epsilon \mid \envSrc, \relation{u}{\sigma} \mid \envSrc, \relation{x}{\typeSrc} 
\eda 
\bda{lc} 
\multicolumn{2}{l}{\myruleform{\envSrc \turns \relation{E}{\typeSrc} ~\gbox{\leadsto e}}} \\ \\


\TyIClass &
\myirule
{ \tau_i = \forall~\overline{\alpha}.~(C~\bar{\alpha}) \To \sem{T_i}
  \quad (\forall \tau_i \in \overline{\relation{u}{T}})
\\
\envSrc,  \overline{\relation{u}{T}} \turns \relation{E}{\typeSrc} ~\gbox{\leadsto e} \quad fresh~\overline{l}}
{ \envSrc \turns
 \relation{{\bf class}~C~\bar{\alpha}~{\bf
    where}~\overline{\relation{u}{T}};~E}{\typeSrc}~\\ 
    \gbox{\leadsto {\bf data}~C~\bar{\alpha}~{\bf =}~C~\overline{\relation{l}{\sem{T}}}~
    \overline{{\bf in~let~} \relation{u}{\tau}~=~l~?(C~\overline{\alpha})}~{\bf in}~e}
}
\\ \\

%%\TyIntL &
%%{ \envSrc \turns n : \tyint \leadsto n } \\ \\

\TyVar &
\myirule
{ \envSrc(x) = \typeSrc }
{ \envSrc \turns \relation{x}{\typeSrc} ~\gbox{\leadsto x} } 
\\ \\

% \TyAnn &
% \myirule
% { \envSrc \turns \relation{E}{\typeSrc} \leadsto e }
% { \envSrc \turns \relation{(\relation{E}{\typeSrc})}{\typeSrc} \leadsto e } 
% \\ \\



\TyAbs &
\myirule
{ \envSrc, \relation{x}{\typeSrc_1} \turns 
  E ~\gbox{\leadsto e}
}
{ \envSrc \turns 
  \relation{\abs{x}{E}}{\typeSrc_1 \to \typeSrc_2} ~\gbox{\leadsto \abs{\relation{x}{\sem{\typeSrc_1}}}{e}}
} 
\\ \\

\TyApp &
\myirule
{ \envSrc \turns \relation{E_1}{\typeSrc_1 \to \typeSrc_2} ~\gbox{\leadsto e_1} \\
  \envSrc \turns \relation{E_2}{\typeSrc_1} ~\gbox{\leadsto e_2}
}
{ \envSrc \turns \relation{E_1~E_2}{\typeSrc_2} ~\gbox{\leadsto e_1 \, e_2}}
\\ \\

\TyLVar &
\myirule
{ \envSrc(u) = \forall \overline{\alpha}.~\overline{\sigma} \To \typeSrc_2 \\
 \theta = [\overline{\alpha} \mapsto \overline{\typeSrc}]\quad \typeSrc_1 = \theta \typeSrc_2 \\
 q_i = ~?{\sem{\theta \sigma_i}} \quad (\forall \sigma_i \in \overline{\sigma})
}
{ \envSrc \turns u : \typeSrc_1 ~\gbox{\leadsto u~\overline{\sem{\typeSrc}}~\overline{{\bf~with~} q}}} 
\\ \\


\TyLet &
\myirule
{ \sigma_1 = \forall \overline{\alpha}. \overline{\sigma_2} \To \typeSrc_1 \\
  \envSrc \turns \relation{E_1}{\typeSrc_1} ~\gbox{\leadsto e_1} \\
  \envSrc, \relation{u}{\sigma_1} \turns \relation{E_2}{\typeSrc_2} ~\gbox{\leadsto e_2}
}
{ \envSrc \turns 
  \relation{{\bf~let~} \relation{u}{\sigma_1} = E_1 {\bf~in~}
    E_2}{\typeSrc_2}  ~\gbox{\leadsto
    (\abs{\relation{u}{\sem{\sigma_1}}}{e_2})~(\overline{\Lambda \alpha.}~
    \overline{\lambda_? \sigma_2.} e_1)}
} 
\\ \\

\TyImp &
\myirule
{ \envSrc \turns \relation{E}{\typeSrc} ~\gbox{\leadsto e} \\
  \envSrc(u_i) = \sigma_i \quad 
%%  q_i = \relation{u_i}{\sem{\sigma_i}} \quad
  (\forall u_i \in \overline{u})
}
{ \envSrc \turns 
  \relation{{\bf~implicit~} \overline{u} {\bf~in~} E}{\typeSrc} ~\gbox{\leadsto 
  (\overline{\lambda_? \sem{\sigma}.} e) \overline{{\bf~with~} u}}
} 
\\ \\

%\TyIVar &
% \myirule
% { }
%{ \envSrc \turns
%  \relation{?}{\typeSrc} ~\gbox{\leadsto  ~?\sem{\typeSrc}}
%} 
%\\ \\



\TyRec &
\myirule
{ \forall i: \left\{\begin{array}{l}
             G(u_i) = \forall \bar{\alpha}.\epsilon \Rightarrow I~\bar{\alpha} \rightarrow T_i \\
             \envSrc \turns E_i : \theta T_i ~\gbox{\leadsto e} \quad \theta = [\bar{\alpha} \mapsto \bar{T}]
             \end{array}\right.}
{ \envSrc \turns
  \relation{I~\overline{u = E}}{C~\bar{T}} ~\gbox{\leadsto C~\overline{u = e}}
} 
\eda
\bda{rcl}
\sem{\alpha} & = & \alpha \\
%%\sem{\tyint} & = & \tyint \\
\sem{\typeSrc_1 \to \typeSrc_2} & = & \sem{\typeSrc_1} \to \sem{\typeSrc_2} \\
\sem{I~\bar{\typeSrc}} & = & I~\sem{\bar{\typeSrc}} \\
\sem{\forall \overline{\alpha}. \overline{\sigma} \To \typeSrc} & = & \forall \sem{\bar{\alpha}}. \sem{\overline{\sigma}} \To \sem{\typeSrc}\\
\eda

}

%if False

To illustrate how we translate the source language constructs into 
$\ourlang$ we first present a complete program written in the source
and then discuss the various constructs involved in that program and 
their corresponding translation.

%endif

The full syntax of the source language is presented in Figure~\ref{f:syntax}. Its use is illustrated
in the program of Figure~\ref{fig:eq}, which comprises an encoding of Haskell's
equality type class \texttt{Eq}.
The example shows that the source language features a simple type of interface $I~\bar{T}$
(basically records), which are used to encode simple forms of type classes. 
Note that we follow Haskell's conventions for records: field 
names |u| are unique and they are modelled as regular functions taking a 
record as the first argument. So a field $u$ with type $T$ in an interface
declaration $I~\bar{\alpha}$ actually has type $\forall \bar{\alpha}.\epsilon \To I~\bar{\alpha} \rightarrow T$. The language also has other conventional programming constructs (such as |let|
expressions, lambdas and primitive types). 

Unlike the core language, we strongly differentiate between simple types $T$
and type schemes $\sigma$ in order to facilitate type inference. 
%%Moreover, as
%%the source language provides implicit rather than explicit type instantiation,
%%the order of type variables in a quantifier is no longer relevant. Hence, they
%%are represented by a set ($\forall \bar{\alpha}$). 
The source language also distinguishes simply
typed variables $x$ from let-bound variables $u$ with polymorphic type
$\sigma$.

%format # = "."
%format E1 = "E_{1}"
%format E2 = "E_{2}"
%format e1 = "e_{1}"
%format e2 = "e_{2}"

\subsection{Syntactic Sugar}

Some syntactic sugar used in our source language.

%{
%format == = "\defeq"
%format . = "."
%format e1
%format E1

\paragraph{General sugar} Explain the sugar

\[ | implicit {-"~\overline{\relation{E}{T}}"-} in E == let {-"
  ~\overline{\relation{u}{T} = E}"-} in implicit {-"~\overline{u}"-} in E| \]

\paragraph{Anonymous Instances} Explain the sugar

\[ | instance {-"\overline{\sigma} \To"-} C {-"~\overline{T_1}~"-}
where {-" \overline{\relation{u}{T_2} = E_2};~ "-} E1 ==  implicit C {-"
  ~\overline{\relation{u}{T_2} = E_2}"-} :
 {-"~\forall~\overline{\alpha}"-}.  {-"\overline{\sigma} \To"-} C
 {-"~\overline{T_1}~"-} in E1| \]

Here $\overline{\alpha} = fv(\overline{\sigma}) \cup fv(\overline{T_1})$ 

\paragraph{Named Instances} Explain the sugar


< instance N@{-"\overline{\sigma} \To"-} C {-"~\overline{T_1}~"-} where {-" \overline{\relation{u}{T_2} = E_2};~ "-} E1
< ==
< let N : {-"~\forall~\overline{\alpha}"-}.  {-"\overline{\sigma} \To"-} C {-"~\overline{T_1}~"-} = C {-"~\overline{\relation{u}{T_2} = E_2}~"-} in implicit N in E1

Here $\overline{\alpha} = fv(\overline{\sigma}) \cup fv(\overline{T_1})$ 

%}

\subsection{Examples}

Figure~\ref{f:type} presents the type-directed translation $G \turns E : T
\leadsto e$ of source language expressions $E$ of type $T$ to core expressions
$e$, with respect to type environment $G$. The type environment collects both
simple and polymorphic variable typings. The connection between source types
$T$ and $\sigma$ on the one hand and core types $\type$ and $\rulet$ on the
other hand is captured in the auxiliary function $\sem{\cdot}$.
We should also remark that while the type system 
in Figure~\ref{f:type} (the non-grey parts) is sufficient to allow the type-directed 
translation, it is incomplete as it does not check whether queries can be resolved or not. 
Performing such checks at the level of the source language is possible, but requires repeating 
some of the infrastructure in Figures~\ref{fig:type} and \ref{fig:resolution2}. 
For simplicity reasons, and since we are mainly interested in the type-directed 
translation, we have avoided that extra machinery here.
For the translation of records, we assume that $\ourlang$ is extended
likewise with records. Like in $\ourlang$, we also assume 
the existence of primitive types like integers, booleans and pairs for the sake of examples. 

\paragraph{|let| and |let|-bound variables}

%if False

Similarly to Haskell, the |let| construct has an optional type
annotation and it introduces a new bound variable |u|. 
When the type annotation is omitted, type inference automatically
derives one. This deviates from the standard Hindley-Milner generalization
in that a type context needs to be inferred as well, i.e., inferring a so-called
\textit{qualified type}~\cite{qual}.
For example, the inferred type for |eqPair| is:

> eqPair : forall a b . {Eq a, Eq b} => (Pair a b) -> (Pair a b) -> Bool

The fact that the context is a set means that it does not matter
in what order the type-inference algorithm puts the rule types in the context.
Consequently, the above type is equivalent to: 

> eqPair : forall a b . {Eq b, Eq a} => (Pair a b) -> (Pair a b) -> Bool

Since $\ourlang$ natively supports such sets, there is no translation work.  

The combination of nested scoping and type inference has an important
consequence. There are two possible types to infer for |f| in the following
example:

> implicit {1: Int} in let f = ? + 1 in ...

namely, |f : {} => Int| and |f : {Int} => Int|, which obviously have different
meanings and a different behavior. The former resolves the query |?| with
the available implicit in the environment, whereas the latter expects the call site
of |f| to provide an |Int| implicit. Since neither type is more general than the other, 
our source language does not have a principal type for every program. However,
from a pragmatic point of view, we prefer the type checker to resolve queries early
on, following the ``let should not be generalized'' principle of Vytiniotis et al.~\cite{let}.
The programmer can still obtain the other behavior by explicitly providing a type signature.

%endif

The rule $\TyLet$ in Figure~\ref{f:type} shows the type-directed translation for |let|
expressions. This translation binds the variable |u| using a regular
lambda abstraction in an expression |e2|, which is the result of the 
translation of the body of the |let| construct (|E2|). This lambda
abstraction is then applied to an expression which has type 
$\forall\overline{\alpha}.\overline{\sigma_2} \Rightarrow T_1$.
When both $\overline{\alpha}$ and $\overline{\sigma_2}$ are empty 
that expression is simply an expression $e_1$, resulting from the 
translation of the expression $E_1$. Otherwise, for each 
$\alpha$ in $\overline{\alpha}$ and for each $\sigma$ in $\overline{\sigma_2}$, 
corresponding type and rule binders are created around the expression $e_1$.

%format T1 = "T_1"

The source language  provides convenience to the user by inferring type
arguments and implicit values automatically. This inference happens in rule
$\TyLVar$, i.e., the use of |let|-bound variables.  That rule recovers the type
scheme of variable |u| from the environment |G|. Then it
instantiates the type scheme and fires the necessary queries to resolve the context. 

\paragraph{Queries} The source language also 
includes a query operator  (|?|). Unlike $\ourlang$ this
query operator does not explicitly state the type; that information is provided
implicitly through type inference. 
For example, instead of using | p1 == p2| in Figure~\ref{fig:eq}, we
could have directly used the field |eq| as follows:

> eq ? p1 p2

When used in this way, the query acts like a placeholder for a value.
The type of the placeholder value can be determined using type-inference. 
Once the type system knows the type of the placeholder
it automatically synthesizes a value of the of the right type from the 
implicit context. 

%%\bruno{Think about type class abstraction, maybe mention it 
%% here!}

The translation  of source language queries, given by the rule
$\TyIVar$, is trivial. To simplify type-inference, the
query is limited to types, and does not support partial resolution. 
%%(although other designs with more powerful queries are possible).
%%In the translated code the query is combined with a rule instantiation
%%and application in order to eliminate the empty rule set. 

%if False

Because the source language also allows a simple form of type annotations (|E :
T|), the programmer can explicitly provide the query type.  This functionality
is important, for example, for higher-rank types that we discuss in
Section~\ref{subsec:type_src}\bruno{Tom, In 5.2 we discuss let
  annotations, not arbitrary annotations... Maybe we can drop
  arbitrary annotations?}.
Translating type annotations $\TyAnn$ is straightforward.

%endif

\paragraph{Implicit scoping} The |implicit| construct is the core scoping 
construct of the source language. It is first used in our example to
make |eqInt|, |eqBool| and |eqPair| available for resolution at the expression

< (p1 == p2, implicit {eqInt2} in p1 == p2) 

Within this expression there is a second occurrence of |implicit|, 
which introduces an overlapping rule (|eqInt2|) that takes
priority over |eqInt| for the subexpression |p1 == p2|.

The translation rule $\TyImp$ of |implicit| into $\ourlang$ also exploits
type-information to avoid redundant type annotations. It is not necessary to annotate the |let|-bound variables 
used in the rule set $\overline{u}$ since that information is recovered from the environment~|G|.

\paragraph{Higher-order rules and implicit instantiation for any type} 
The following example illustrates higher-order
rules and implicit instantiation working for any type in the source language.

%format dots = "\ldots"
%format qu = "~?~"

< let show : forall a . {a -> String} => a -> String = qu in
< let showInt : Int -> String = dots in
< let comma : forall a . {a -> String} => [a] -> String = dots in 
< let space : forall a . {a -> String} => [a] -> String = dots in
< let o :  {Int -> String, {Int -> String} => [Int] -> String} 
<            => String = show [1,2,3] in
< implicit showInt in
< (implicit comma in o, implicit space in o)

For brevity, we have omitted the implementations of |showInt|, |comma| and |space|;
but |showInt| renders an |Int| as a |String| in the conventional way, while
|comma| and |space| provide two ways for rendering lists.  Evaluation of
the expression yields |("1,2,3","1 2 3")|. Thanks to the implicit rule
parameters, the contexts of the two calls to |o| control how the lists
are rendered.

This example differs from that in Figure~\ref{fig:eq} in that instead of 
using a \emph{nominal} interface type like |Eq|, it uses
standard functions to model a simple concept for pretty printing values. 
The use of functions as implicit values is similar
to \emph{structural} matching of concepts, since only the type of the function 
matters for resolution. 

% \paragraph{Higher-order rules and first-class interfaces} The
% following example illustrates the source language support for
% higher-order rules and first-class interfaces.
% 
% %format r1 = "\Varid{r_1}"
% %format r2 = "\Varid{r_2}"
% 
% < let buildPair : forall a . {a} => Pair a a = (?,?) in
% < let r1 : {forall a . {a} => Pair a a, Int} => Pair Int Int = qu in 
% < let r2 :  {forall a . {a} => Pair a a, Eq Int} =>
% <             Pair (Eq Int) (Eq Int) = qu in 
% < let i : Int = 5 in
% < let eqInt : Eq Int =  Eq {eqImpl = primEqInt} in
% < implicit {i, eqInt, buildPair} in (r1,r2)
% 
% Here, |buildPair| takes an implicit value of some type |a|
% and builds a pair of two of these. The definitions 
% |r1| and |r2| show the use of higher-order rules in the source
% language. Both definitions require an implicit rule of type |forall a
% . {a} => Pair a a|. In |r1| that rule is used in combination with an 
% implicit value of type |Int|, whereas in |r2| an implementation of |Eq
% Int| is required instead. Using those definitions and som
%  
%  
% 
% 
% , because interfaces are 
% just regular types, it also supports abstracting over these
% interfaces. 


%if False

$\ourlang$ is designed to be a convenient target language for implicit
programming mechanisms. $\ourlang$, like many other implicit
programming mechanisms, uses \emph{sets} of implicit arguments (or
constraints). Choosing sets in the source language is a natural choice
for the source language if we want to maximize the amount of
type-inference. Because $\ourlang$ natively supports sets it
considerably simplifies the translation of such source languages.
Haskell is an example of one language that uses sets of constraints,
and our source language follows a similar design to that of Haskell.

Records are shown in the syntax, but they are a standard extension. 
We do not show the translation rule for records.

%endif


%% \subsection{Type System}
%% \label{subsec:type_src}

%if False

\paragraph{Overlap Within a Set} Overlap within a set, a feature that GHC supports for Haskell's global
type class scope, can also be encoded.
Consider the following program:

> let eqList : forall a . {Eq a} => Eq [a] = dots in
> let eqString : Eq [Char] = dots in
> implicit {eqList, eqString} in 
>   ("Hello" == "hello", [1,2,3] == [2,1,3])

The set |{eqList, eqString}| is overlapping because |eqString| is 
more specific than |eqList|. $\ourlang$ does not allow such a set
directly. However, we can easily transform overlapping sets into 
non-overlapping sets using nested scoping: 

> dots implicit {eqList} in implicit {eqString} in dots

The basic idea is to stratify an overlapping set into non-overlapping
sets using the ordering relation on types.

%endif

%-------------------------------------------------------------------------------
%if False
\subsection{Type Inference}
\label{subsec:type_src}

We address the two main issues of type inference for our source language:
local assumptions and higher-rank types.

\paragraph{Local Assumptions}
Generalized Algebraic Data Types~(GADTs) \cite{xi:gadts} have shown that \textit{local
assumptions} preclude principal types~\cite{schrijvers:outsidein}. This is no different in our
setting where the |implicit| construct makes local assumptions about the
availability of values in the implicit environment. For example, consider the
program:

> implicit {3,True} in ? 

The above expression has the types \tyint{}, \tybool{} and $\forall
a.\{a\} \To a$, none of which is more general than the other two.
This makes type inference problematic, as it does not know which
of the several most general types is intended by the programmer.


Fortunately, the \textsc{OutsideIn}(X) type inference approach~\cite{schrijvers:outsidein,vytiniotis:outsidein} provides
an adequate solution to the problem of local assumptions. It conservatively
accepts (most) programs with a unique most general type and rejects
\textit{all} programs with multiple most general types. While first
developed for GADT and type class assumptions, \textsc{OutsideIn}(X) is
parametric in the domain X of assumptions. To deal with local assumptions, we
instantiate X to implicit rules.

\paragraph{Higher-Rank Types and Higher-Order Rules}
%endif

\subsection{Extensions}\label{subsec:extensions}

The goal of our work is to present a minimal and general framework for 
implicits. As such we have avoided making assumptions about extensions 
that would be useful for some languages, but not others. 

In this section we briefly discuss some extensions that would be useful in
the context of particular languages and the implications that they
would have in our framework.

%if False

While the source language presented in this section is already quite 
interesting for GP, there are still many features that we have not
discussed.

%endif 

\paragraph{Full-blown Concepts} The most noticeable feature that was not
discussed is a full-blown notion of concepts. One reason not to commit
to a particular notion of concepts is that there is no general
agreement on what the right notion of concepts is.  For example, following Haskell type classes,
the C++0x concept proposal~\cite{concepts} is based
on a \textit{nominal} approach with \textit{explicit} concept refinement, while
Stroustrup favors a \textit{structural} approach with \textit{implicit} concept refinement
because that would be more familiar to C++
programmers~\cite{stroustrup09concepts}. Moreover, various other proposals for
GP mechanisms have their own notion of interface: Scala uses standard OO
hierarchies; Dreyer et al. use ML-modules~\cite{modular}; and in
dependently typed systems (dependent) record types are used~\cite{coqclasses,instanceargs}.

An advantage of $\ourlang$ is that no particular notion of
interface is imposed on source language designers. Instead, language
designers are free to use the one they prefer. In
our source language, for simplicity, we opted to add a very simple
(and limited) type of interface. But existing language
designs~\cite{implicits,modular,coqclasses,instanceargs} offer
evidence that more sophisticated types of interfaces, including some
form of refinement or associated types, can be built on top of
$\ourlang$. 

%if False

Although
the interfaces that we present in this section allow us to express
some simple types of concept-style interfaces (like the equality type class), they 
do not provide an account for features like concept refinement (or
subclasses) or associated types. 

There are two main reasons why we did not provide a richer notion of
concepts. Firstly, the focus of our work is on implicits and the idea that 
implicit instantiation should not be coupled with a particular type 
of interface. Many researchers have argued that when the base
language has a suitable notion of interface, then building type
classes or concepts on top of it is easy. Dreyer et al. made this
argument for ML-modules, various theorem provers build a simple 
implicit instantiation mechanism around native records~\cite{}, and
ofcourse Scala reuses the OO system to model concept-like interfaces.
Secondly, while there is a general agreement that implicit
instantiation is useful, there is not a uninimous consensus about what 
the right notion of concepts is. 

Our language provides a simple, 
record-style, type of interface. While these interfaces are already
good enough to model simple types of concepts or type classes, there 
is no mechanism for concept refinement or subclasses. 

%endif

\paragraph{Type Constructor Polymorphism and Higher-order Rules}
Type constructor polymorphism is an advanced, but highly powerful GP feature
available in Haskell and Scala, among others.  It allows abstracting container
types like |List| and |Tree| with a type variable |f|; and applying the
abstracted container type to different element types, e.g., |f Int| and |f Bool|.

This type constructor polymorphism leads to a need for higher-order rules: rules
for containers of elements that depend on rules for the elements. The 
instance for showing values of type |Perfect f a| in Section~\ref{sec:intro}, is a typical example of this need. 

Extending $\ourlang$ with type constructor polymorphism is not hard. 
Basically, we need to add a kind system and move from a System~$F$-like 
language to a System $F_{\omega}$-like language.  

%if False

To illustrate the use of higher-order rules we assume 
that our language supports Haskell-style datatypes and 
consider the non-regular tree, similar to the example discussed by 
Hinze and Peyton Jones~\shortcite{derivable}:

> data Perfect f a = Leaf a | Branch (Perfect f (f a))

%% This type generalizes the well-known perfectly balanced tree type, where |f| is |Tuple|
%% with |data Tuple a = Tuple a a|.
For processing this data type, e.g., converting it to a string, 
a higher-rank type is required:
  
< showPerfect  :   forall f a . {forall b. {Show b} => Show (f b), Show a} 
<               =>  Perfect f a -> String
< showPerfect (Leaf x)     = show x
< showPerfect (Branch xs)  = "Branch " ++ showPerfect xs

where |show : forall a. {Show a} => a -> String|.

The type of |showPerfect| is a higher-order rule because it assumes a polymorphic rule
type, |forall b. {Show b} => Show (f b)|, that itself contains an assumption.
Note also that the assumption itself is polymorphic in |b|, which makes the
overall type of rank 2. This polymorphic higher-order assumption is necessary because the type of
the elements depends on the number of levels in the tree.

The second clause of |showPerfect| triggers two resolutions for filling in the
two assumptions (|forall b. {Show b} => Show (f b)| and |Show (f a)|)  of the
recursive call |showPerfect xs|.  Both are performed with respect
to the same environment that contains the two assumptions of |showPerfect|'s
type signature. Obviously, the former query directly corresponds to the rule in
the environment and thus is easily resolved. However, |Show (f a)| requires a
recursive resolution step, composing the two rules in the environment.

%endif

%if False

Type inference of higher-rank types is a particularly tough challenge for which
several approaches have been proposed in the literature~\cite{qml,flexibletypes,mlf}, each
of which imposes certain restrictions. 
%As this is not the main focus of this paper, we restrict
We restrict
automatically inference to rank-1 types, and have the programmer
explicitly annotate higher-rank types.

%endif


\paragraph{Subtyping} Languages like Scala or C++ have subtyping. Subtyping
would require significant adaptations to $\ourlang$.  Essentially, instead of
targetting System F, we would have to target a version of System F with
subtyping. In addition, the notion of matching in the lookup function
$\lookup{\env}{\type}$ would have to be adjusted. While subtyping is a useful feature, some
language designs do not support it because it makes the system more complex and
interferes with type-inference.  

\paragraph{Type-inference}
Languages without subtyping (like Haskell or ML) make it easier to
support better type-inference. Since we do not use subtyping, 
it is possible to improve support for type-inference in our
source language. In particular, we currently require a type annotation 
for |let| expressions, but it should be possible to make that
annotation optional, by building on existing work 
for the GHC Haskell compiler~\cite{schrijvers:outsidein,vytiniotis:outsidein}.


%if False

\subsection{$\ourlang$ as a Target Language}



Consider the program in Figure~\ref{fig:eq}. This program illustrates how
we encode the equality type class and several instances in our
source language. As we can see the source language includes record
types (which are used to encode type classes) as well as other
conventional programming constructs (such as |let| expressions,
lambda's and a few primitive types). The full syntax is presented in
Figure~\ref{f:syntax}.

\tom{We should drop this paragraph, since the contexts are sets already in 
the core.}
$\ourlang$ is designed to be a convenient target language for implicit
programming mechanisms. $\ourlang$, like many other implicit
programming mechanisms, uses \emph{sets} of implicit arguments (or
constraints). Choosing sets in the source language is a natural choice
for the source language if we want to maximize the amount of
type-inference. Because $\ourlang$ natively supports sets it
considerably simplifies the translation of such source languages.
Haskell is an example of one language that uses sets of constraints,
and our source language follows a similar design to that of Haskell.

\paragraph{Scala style implicits}
However $\ourlang$ is expressive enough to deal with languages that 
make a different choices. For example in Scala, because type-inference 
is not as important,  implicit argument are essentially passed as a
tuple of several such implicit argument. We can encode this semantics 
by using a singleton set with a tuple. For example, the 
Scala definition:

> def func[a](x : a)
>   (implicit eqD : Eq[a], showD : Show[a]) : String = dots

could be encoded as:

> let func : forall a . {(Eq a, Show a)} => a -> String = 
>   let (eqD, showD) = ?(Eq a, Show a) in dots



Besides having a nice logical interpretation (as we have
discussed in Section~\ref{}), sets are useful for type-inference. The
basic idea is not different from what Haskell does. The only real
difference is that methods,

As Figure~\ref{fig:eq} illustrates all 
definitions except |==| can have their types inferred.

In particular, one of the goals 
of the design of $\ourlang$ is to make it a friendly target for source 
languages that have good support type-inference. 
type-inference 

In those languages 
implicit arguments (or constraints) are typically passed in sets.  
Sets are important because they facilitate type inference, since the
order of the implicit arguments does not matter. For example, the 
type of |eqPair| can be either:

> eqPair : {Eq a, Eq b} => (a,b) -> (a,b) -> Bool

or 

> eqPair : {Eq b, Eq a} => (a,b) -> (a,b) -> Bool

because the constraints are sets, these two types are
equivalent and both types are valid for |eqPair|. Since the implicit 
calculus natively supports such sets, translating programs from the 
source language to $\ourlang$ becomes much simpler since no 
encodings of sets in terms of other constructs is needed. 

Another way in which sets are important in source languages is that
usually many implicit arguments are introduced  at once in the
implicit environment. In Haskell 98, for example, there is a global
\emph{set} of non-overlapping instances that is visible in a program. 
Similarly, in mechanisms like modular type classes, which allow 
only one level of nested scoping, a set of implicit (non-overlapping) 
instances is introduced at once. This is similar to our  first use of 
|implicit| in Figure~\ref{fig:eq}. 

Precisely defining non-overlapping sets is tricky, but if the target
language does not support sets natively, this effort must be delegated 
to the source language. Because $\ourlang$ adopts sets natively, it
comes with a built-in definition of non-overlapping sets that can be
readily reused by a source language.

While it is possible to have a simpler target language that does away 
with sets --- after all this is what most elaboration translations do
--- this puts a heavy burden on the designer of the source language, 
which has to encode sets on the target language and define all relevant 
properties of sets (like non-overlapping sets) from scratch. 

\paragraph{Overlapping Within a Set} Overlapping within a set, as
allowed, for example in Haskell extensions, can be encoded in
$\ourlang$. For example, consider the following program:


> let eqList : forall a . {Eq a} => [a] -> String = dots in
> let eqString : [String] -> String = dots in
> implicit {eqList, eqString} in 
>   (eq "Hello" "hello", eq [1,2,3] [2,1,3])

The set |{eqList, eqString}| is overlapping because |eqString| is 
more specific than |eqList|. $\ourlang$ does not allow such set
directly. However, we can easily transform overlapping sets into 
non-overlapping sets using nested scoping: 

> dots implicit {eqList} in implicit {eqString} in dots

The basic idea is to stratify an overlapping set into non-overlapping
sets using the ordering relation on types.\bruno{Do we want to
  implement this on the translation?}



\paragraph{Type-directed translation}
The type-directed translation from the source language 
into the implicit calculus extended with records is presented 
in Figure~\ref{}. 

One important difference between the implicit calculus and this 
source language is that in the source language the query operator 
(|?|) does not explicit take the type to be queried as an argument. 
Rather, to achieve the same result, a type annotation must be used 
instead. As we shall discuss next, this design choice allows 
the query operator to interact with type-inference to perform 
queries, while still allowing explicit queries via type annotations 
as done here.

In our source
language the |let| construct supports optional type annotations and
for many programs, including all other let definitions, it is possible
to omit such annotations.  The source language also allows arbitrary
expressions to have optional type annotations. In this respect, our
source language follows Haskell implementations like GHC, which also
support a similar model of optional type annotations~\cite{}.

The query operator (|?|) also benefits from type inference. When used
in a context where type inference is capable of precisely determining
the type of the expression, |?| effectively becomes a placeholder that
instructs the compiler to automatically find a value of the given type
from the environment. For example, instead of using | p1 == p2|, we
could have directly used the field |eq| as follows:

> eq ? p1 p2

The functionality provided by queries when used in this way is
somewhat similar to placeholders (|_|) in Coq (and other theorem
provers).

\bruno{Mention context reduction/late binding?}

%% In such languages, the ability to infer constraints automatically is crutial. 

To illustrate the use of the implicit calculus to model a more
realistic language with IP features, we designed a Haskell-like source
language. This language includes records, which are used to encode
type classes, and it also incorporates several constructs that
combine implicit calculus constructs with standard lambda calculus
constructs. A type-directed translation from the source language into
the implicit calculus extended with records is presented in
Section~\ref{}.

%format p1 = "\Varid{p}_1"
%format p2 = "\Varid{p}_2"
%format eqInt = "\Varid{eqInt_1}"
%format eqInt2 = "\Varid{eqInt_2}"
%format eqImpl = "\Varid{eq}"

\begin{figure}

< record Eq a = {eqImpl : a -> a -> Bool}
<
< let  (==) : forall a . {Eq a} => a -> a -> Bool = eqImpl (? : Eq a) in
< let  eqInt    = Eq {eqImpl = primEqInt} in
< let  eqInt2  = Eq {eqImpl = \x y # isEven x && isEven y} in
< let  eqBool  = Eq {eqImpl = primEqBool} in
< let  eqPair   = Eq {eqImpl = \x y # 
<       fst x == fst y && snd x == snd y} in
< let p1 = (4,True) in
< let p2 = (8,True) in
< implicit {eqInt, eqBool, eqPair} in
< 
< (p1 == p2, implicit {eqInt2} in p1 == p2) 

\caption{Encoding the equality type class.}

\label{fig:eq}

\end{figure}

\bruno{Encoding may give the wrong impression; maybe rephrase latter.}
\paragraph{Encoding type classes} Figure~\ref{fig:eq} shows a complete
program in our source language. Rather than providing type classes
directly, in this source language we encode type classes using records
and type class instances as regular definitions. This simple encoding
essentially the same as the one proposed by \cite{} in Scala, but here
we use records rather than object-oriented interfaces and objects.

A type class like |Eq|, which in Haskell would be written as:

< class Eq a where
<    (==) :: a -> a -> Bool

is encoded as a record (|Eq|) with fields of the appropriate
type. However, such fields do not directly encode type class 
methods because they require an explicit |Eq a| record as an 
argument. As such, in order to encode methods, we want to 
define a function that takes the record (type class) argument 
implicitly. Fortunately this is quite easy todo as illustrated 
by the |(==)| definition:

< let  (==) : forall a . {Eq a} => a -> a -> Bool = eqImpl (? : Eq a)

The basic idea is that if we define the type of |(==)| as a rule type 
with an |Eq a| assumption, then we can query for that type 
in the definition and retrieve the value for |Eq a| from the rule
environment, rather than having to explicitly pass such value.

One important difference between the implicit calculus and this 
source language is that in the source language the query operator 
(|?|) does not explicit take the type to be queried as an argument. 
Rather, to achieve the same result, a type annotation must be used 
instead. As we shall discuss next, this design choice allows 
the query operator to interact with type-inference to perform 
queries, while still allowing explicit queries via type annotations 
as done here.

\paragraph{Type Inference} In Figure~\ref{fig:eq} it is important to
note that the definition of |(==)| is the only place in the program
where we need to provide explicit type annotations. In our source
language the |let| construct supports optional type annotations and
for many programs, including all other let definitions, it is possible
to omit such annotations.  The source language also allows arbitrary
expressions to have optional type annotations. In this respect, our
source language follows Haskell implementations like GHC, which also
support a similar model of optional type annotations~\cite{}.

As usual in an Hindley-Milner language, type-inference of |let|
expressions performs generalization and, like in Haskell, during this
process the required assumptions are inferred too. As such, the
inferred type for a definition like |eqPair| is:

< eqPair : forall a b . {Eq a, Eq b} => Eq (a,b)

Note that, in some sense, in our source language it is possible to
infer more types than a language like Haskell. In particular,
definitions like |eqPair| would correspond to Haskell
instances rather than function definitions. However, unlike function 
definitions, Haskell instances require all constraints to be explicitly stated.
In our source language, even though |eqPair| is later used in the same 
way as an Haskell instance, all the assumptions can be inferred.

As we shall discuss in more detail in Section~\ref{}, there
is no guaranteed that the inferred type of |let| definitions is the
principal type. Again this is similar to existing Haskell
implementations, in which the inferred type is also not 
guaranteed to be the principal type. Nevertheless the Haskell
experience has shown that it is rather convenient to infer those 
types, even if they are not the principal ones.

The query operator (|?|) also benefits from type inference. When used
in a context where type inference is capable of precisely determining
the type of the expression, |?| effectively becomes a placeholder that
instructs the compiler to automatically find a value of the given type
from the environment. For example, instead of using | p1 == p2|, we
could have directly used the field |eq| as follows:

> eq ? p1 p2

The functionality provided by queries when used in this way is
somewhat similar to placeholders (|_|) in Coq (and other theorem
provers).

\paragraph{Context Reduction and Late Binding}

Context reduction refers to the ability of simplifying the rule
assumptions during the type-inference process. It is an important
feature of IP mechanisms like Haskell type classes,
which are intimately connected to type-inference. Consider the 
following variation of the example in Figure~\ref{fig:eq}:

%format dots = "\ldots"
%format eqPair2 = "\Varid{testPair}"

< dots
< implicit {eqInt, eqBool, eqPair} in
<
< let eqPair2 = \p1 p2 # (snd p1, fst p1) == p2 in
< dots

Here we define a variant of equality on pairs, which first swaps the
two elements of the first pair and then compares the resulting pair
with the other pair. The inferred type for this function is:

< eqPair2 : forall a b . {Eq a, Eq b} => (a,b) -> (b,a) -> Bool

Notably, instead of the assumption |{Eq (a,b)}|, which would appear to
be the assumption that follows directly from the code, we get |{Eq a,
  Eq b}|. This is because there is a rule, |eqPair|, on scope and this
rule is used to simplify the assumptions via context reduction. 
If |eqPair| would not be on scope then the type of |eqPair2|
would indeed be:

< eqPair2 : forall a b . {Eq (a,b)} => (a,b) -> (b,a) -> Bool

In the implicit calculus we follow Haskell closely with respect to
context reduction in two ways. Firstly, the inference process
tries to eagerly resolve all the assumptions using the information
available from the rule environment. Secondly, like in GHC Haskell, 
it is possible to control context reduction through explicit type 
signatures. So, if we wanted to resolve the assumption for pairs in 
|eqPair2| latter, we could do so by wrtting the following instead:

 
< let eqPair2 : forall a b . {Eq (a,b)} => (a,b) -> (b,a) -> Bool = 
<    \p1 p2 # (snd p1, fst p1) == p2 in

In summary, type-inference takes an early binding approach 
and tries to resolve all assumptions as soon as possible. However, 
it is possible to get late binding, by explicitly annotating the
programs. 

\paragraph{Overriding}

\bruno{Need to motivate why overriding can be better than nested 
scoping. |with| should not just be syntactic sugar for nested scoping}.
In our source language it is also possible to override the implicit
rules through a restricted use of rule application (|with|).

So far |implicit|, which is a construct that combines rules and rule 
applications, has been used to  

\paragraph{Higher-order predicates in the source language}

\bruno{Some fixes/ perhaps a bit more work on the interpreter 
needed to discuss this}

%%if False

\subsection{Flexible Implicit Values}
\label{subsec:flexible}

We allow arbitrary types in rule types. This is different from type
class-like systems. The type class-like systems can be modelled as
simple logic language with Horn clauses of predicates on
types. Rather, our system is closer to Scala implicits~\cite{scala}.

Using arbitrary types for the assumptions has more flexibility than
using only predicates on types. Because of this limitation, some
Haskell programs try to encode natural number using type-level Church
numeral to do the very same thing like this:

\[  
\begin{array}{l}
  \relation{f}{\myset{\tyint} \To \tyint} \\ 
  f = \ruleabs{(\myset{\tyint} \To \tyint)}{(?\tyint + 1)}
\end{array}
\]
\[  
\begin{array}{l}
  \ruleapp{f}{\myset{\relation{\ruleabs{(\epsilon \To
          \tyint)}{1}}{\epsilon\To \tyint}}}
\end{array}
\]

\subsection{Lexical Scoping}
\label{subsec:lexical}

We support lexical scoping of rule environments. Consider the
following example:
\\
\[  
\begin{array}{l}
  \ruleapp
  {\ruleapp{f}{\myset{\relation{2}{\tyint}}}}
  {\myset{\relation{1}{\tyint}}}
\end{array}
\]
\\
The rule $f$ is now put under two environments. 

Under the nesting, we choose the closest one from the given rule.

\subsection{Overlapping}
\label{subsec:overlapping}

We allow overlapping of rules. 

\[
\begin{array}{l}
  \relation{f}{\forall \alpha. \alpha \to \alpha} \\
  f = 
  \ruleapp
  {(\ruleabs
    {(\forall \alpha.
      \myset{\forall \beta. \beta \to \beta, \tyint \to \tyint}
      \To \alpha \to \alpha)
    }
    {(?\alpha \to \alpha)})\\\quad\quad}
  {\myset{
      \relation{\lambda x. x + 1}{\tyint \to \tyint},
      \relation{\lambda x. x}{\forall \gamma. \gamma \to \gamma}
    }}
\end{array}
\]

%endif

%if False

\subsection{Syntax}
\label{subsec:syntax_src}

This section introduces a source language (and a variation), 
that are good for type inference.

%endif



%%% Local Variables: 
%%% mode: latex
%%% TeX-master: "../Main"
%%% End: 



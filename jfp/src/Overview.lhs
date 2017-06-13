%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Rule.fmt

%format === = "\cong"

\section{Overview}
\label{sec:overview}

This section summarises the relevant background on type classes, IP 
and coherence, and introduces $\ourlang$'s key features for ensuring coherence.
We first discuss Haskell type classes, the oldest
and most well-established IP mechanism, then compare them to
Scala implicits, and finally we introduce the coherence approach taken in $\ourlang$.

\subsection{Type Classes and Implicit Programming}\label{subsec:tclasses}

Type classes enable the declaration of overloaded functions like comparison,
pretty printing, or parsing.

> class Ord a where
>   (<=) :: a -> a -> Bool
> class Show a where
>   show :: a -> String
> class Read a where
>   read :: String -> a

A type class declaration consists of: a class name, such as |Ord|, |Show|
or |Read|; a type parameter, such as |a|; and a set of method declarations,
such as those for |(<=)|, |show|, and |read|. Each of
the methods in the type class declaration should have at least one
occurrence of the type parameter |a| in their signature.
% (either as an argument or as a return type).
% The type parameter may be neither an argument nor a return type,
% as in showList :: [a] -> String.

\paragraph{Instances and Type-Directed Rules}
Instances implement type classes.
% Implementations 
% of type classes are provided by type class instances. 
% In our terminology, borrowed from the implicit calculus, 
% instances are synonymous with rules.
For example, |Ord| instances for integers, characters, and pairs 
can be defined as follows:

> instance Ord Int where
>   x <= y  =  primIntLe x y
> instance Ord Char where
>   x <= y  =  primCharLe x y
> instance (Ord a, Ord b) => Ord (a, b) where
>   (x,x') <= (y,y') = x < y || (x == y && x' <= y')

\noindent The first two instances provide the implementation of ordering for integers
and characters, in terms of primitive functions.
The third instance is more interesting, and provides the
implementation of ordering for pairs. In this case, the ordering
instance itself \emph{requires} an ordering instance for both
components of the pair. These requirements are resolved 
by the compiler using the existing set of instances in a process called 
\emph{resolution}.  
Using |Ord| we can define a generic sorting function

> sort :: Ord a => [a] -> [a]

\noindent that takes a list of elements of an arbitrary type |a| and
returns a list of the same type, as long as ordering is supported
for type |a|. The body of the function may refer to |<=| on type |a|.

\paragraph{Implicit Programming}
Type classes are an implicit 
programming mechanism because implementations of type class operations 
are automatically \emph{computed} from the set of instances during the 
resolution process. 
For instance, a call to |sort| only type checks if a suitable type class instance can be
found. Other than that, the caller does not need to worry about the
type class context, as shown in the following interaction with a
Haskell interpreter: 

< Prelude > sort [ (3,'a'), (2,'c'), (3,'b') ]
< [(2,'c'),(3,'a'),(3,'b')]

\noindent In this example, the resolution process combines the three |Ord| instances 
to find a suitable implementation for |Ord (Int,Char)|.  The declarations given
are sufficient to resolve an infinite number of other instances, such as
|Ord (Char,(Int,Int))| and the like.

\paragraph{One Instance Per Type} A characteristic of
(Haskell) type classes is that only one instance is allowed for a
given type. For example, it is forbidden to include the alternative ordering
model for pairs

> instance (Ord a, Ord b) => Ord (a, b) where 
>   (xa,xb) <= (ya,yb) = xa <=ya && xb <= yb

in the same program as the previous instance because the
compiler automatically picks the right type class instance based on
the type parameter of the type class. If there are two
type class instances for the same type, the compiler does not
know which of the two to choose.

\subsection{Coherence in Type Classes}
\label{sec:overview-coherence}

An IP design is \emph{coherent} if
any valid program has exactly one meaning (that is,
the semantics is not ambiguous). 
Haskell imposes restrictions to guarantee
coherence. For example, the expression:

> show (read "3") == "3" 

\noindent is rejected in Haskell due to \emph{ambiguity} of 
\emph{type class resolution}~\cite{qual}.  Functions |show| and
|read| print and parse values of any type |a| that instantiates
the classes |Show| and |Read|.  The program is rejected because
there is more that one possible choice for |a|, for example
it could be |Int|, |Float|, or |Char|. 
Choosing |a=Float| leads to |False|,
since showing the float |3| would result in |"3.0"|,
while choosing |a=Int| leads to |True|.

\paragraph{Overlapping and Incoherent Instances} 
Advanced features of type classes, such as overlapping
instances, require additional restrictions to
ensure coherence.  The following program illustrates the issues:

> class Trans a where trans :: a -> a
> instance Trans a where trans x = x
> instance Trans Int where trans x = x+1

\noindent This program declares a type class |Trans a| for defining
transformations on some type |a|. The first instance provides a default
implementation for any type, the identity transformation.  The second instance
defines a transformation for integers only. 

The overlapping declarations are clearly incoherent,
since it is unclear whether |trans 3| should return
|3| using the first instance, or |4| using the second instance.
Because the second instance is more specific, one 
might expect that it supersedes the first one; and that is indeed how
Haskell assigns a meaning to overlapping instances.

But now consider the following declaration.

> bad :: a -> a
> bad x = trans x  -- incoherent definition!

If Haskell were to accept this definition, it
would have to implement |trans| using the first instance,
since |trans| is applied at the arbitrary type |a|.
Now |bad 3| returns |3| but |trans 3| returns |4|,
even though |bad| and |trans| are defined to be
equal, a nasty impediment to equational reasoning!

For this reason Haskell rejects the program by default. A programmer who really
wants such behaviour can enable the \emph{IncoherentInstances} compiler flag,
which allows the program to typecheck. But the use of incoherent instances is
greatly discouraged.

\paragraph{Global Uniqueness of Instances} A consequence 
of having both coherence and at most one instance of a type class 
per type in a program is \emph{global uniqueness} of instances~\cite{uniqueness}. That is, 
at any point in the program type class resolution for a particular 
type always resolves to the same value. 
The usefulness of this property is illustrated by a library that
provides a datatype for sets that is polymorphic in the elements along with a
|union| operation:

< union :: Ord a => Set a -> Set a -> Set a

\noindent For efficiency reasons the sets are represented by a
data structure that orders the elements in a particular way. 
It is natural to rely on the |Ord| type class to deal with ordering for the particular type |a|.  To preserve the
correct invariant, it is crucial that the ordering of elements in the
set is always the same. The global uniqueness property guarantees this. If two
distinct instances of |Ord| could be used in different parts of the
program for the same type, then it would be possible to construct within the
same program two sets using two different orderings (say ascending and
descending order), and then break the ordering invariant by
|union|-ing those two sets.

Although global uniqueness is, in principle, a property that should hold in
Haskell programs, Haskell implementations actually violate this property in
various circumstances~
\footnote{\url{http://stackoverflow.com/questions/12735274/breaking-data-set-integrity-without-generalizednewtypederiving}}.
In fact it is acknowledged that providing a global uniqueness check is quite 
challenging for Haskell implementations~\footnote{\url{https://mail.haskell.org/pipermail/haskell-cafe/2012-October/103887.html}}.

\subsection{Scala Implicits and Incoherence}

Scala implicits~\cite{implicits} are an interesting alternative IP
design. Unlike type classes, implicits have locally scoped
rules. Consequently Scala does not have the global uniqueness
property, since different ``instances'' may exist for
the same type in different scopes. Another interesting difference
between implicits and type classes is that values of any type can be
used as implicit parameters; there are no special constructs analogous
to type class or instance declarations. Instead, implicits are modelled
with ordinary types. They can be abstracted over and do not suffer
from the second-class nature of type classes. Such features mean that 
Scala implicits have a wider range of applications than type classes. 
For example, they can be used to solve the problem of 
\emph{implicit configurations}~\cite{Kiselyov04} naturally. The following 
example, adapted from Kiselyov and Shan, illustrates this:

\begin{code}
def add(a : Int, b : Int)(implicit modulus : Int) = (a + b) % modulus  
def mul(a : Int, b : Int)(implicit modulus : Int) = (a * b) % modulus  
implicit val defMod : Int = 4       
def test = add(mul(3,3), mul(5,5)) // returns 2
\end{code}

\noindent Here the idea is to model \emph{modular arithmetic}, 
where numbers
that differ by multiples of a 
given modulus are treated as identical.
For example 2 + 3 = 1 (mod 4) because 2 + 3 and 1 differ 
by a multiple of 4. The code shows the definition of 
addition and multiplication in modular arithmetic. 
In Scala |%| is modulo division. Both \emph{add}ition and \emph{mul}tiplication 
include a third (implicit) parameter, which is the modulus 
of the division. Although the modulus could be passed explicitly 
this would be extremely cumbersome. Instead it is desirable that 
the modulus be passed implicitly. Scala implicits allow this, by simply marking 
the |modulus| parameter in |add| and |mul| with the |implicit| keyword. 
The third line shows how to set up an implicit value for the modulus. 
Adding |implicit| before |val| signals that the value being defined 
is available for synthesising values of type |Int|. 
Finally, |test| illustrates how expressions doing modular arithmetic 
can be defined using the implicit modulus. Because Scala also 
has local scoping, different modulus values can be used under 
different scopes.

\paragraph{Incoherence in Scala}
Although Scala allows \emph{nested} local scoping and overlapping rules,
\textit{coherence} is not guaranteed. Figure~\ref{fig:scala} illustrates
the issue briefly, based on the example from Section~\ref{sec:overview-coherence}.
Line~(1) defines a function |id| with type parameter |a|, which is simply
the identity function of type |a => a|.
The |implicit| keyword in the declaration specifies that this value may
be used to synthesise an implicit argument.
Line~(2) defines a function |trans| with type parameter |a|,
which takes an implicit argument |f| of type |a => a| and returns |f(x)|.
Here the |implicit| keyword specifies that the actual argument should not be
given explicitly; instead argument of the appropriate type will be synthesised from
the available |implicit| declarations.


%format v1 = "\Varid{v_1}"
%format v2 = "\Varid{v_2}"

\begin{figure}
\small
\begin{code}
trait A {
   implicit def id[a] : a => a = x => x		   // (1)
   def trans[a](x : a)(implicit f: a => a) = f(x)  // (2)
}
object B extends A {
   implicit def succ : Int => Int = x => x + 1	   // (3)
   def bad[a](x:a) : a = trans[a](x)		   // (4) incoherent definition!
   val v1 = bad[Int](3)				   // (5) evaluates to 3
   // val v2 = trans[Int](3)		           // (6) substituting bad by trans is rejected
}
\end{code}

\caption{Nested Scoping with Overlapping Rules in Scala}

\label{fig:scala}

\end{figure} 

In the nested scope, line~(3) defines function |succ| of type |Int =>
Int| that takes argument |x| and returns |x+1|. Again, the |implicit|
keyword in the declaration specifies that |succ| may be used to
synthesise implicit arguments. Line~(4) defines a function |bad| with
type parameter |a| which takes an argument |x| of type |a| and returns
the value of function |trans| applied at type |a| to argument
|x|. Line~(5) shows that, as in the earlier example and for the same
reason, |bad(3)| returns |3|. As with the Haskell example, accepting
this definition is an equally nasty impediment to equational
reasoning, since performing simple equational reasoning would lead to
a different result. However unlike in Haskell, it is the intended
behaviour: it is enabled by default and cannot be disabled.
Interestingly the expression in line~(6), which is accepted in Haskell, is actually rejected in Scala.\footnote{We have observed this behavior for Scala 2.11; for lack of a specification, it is not clear to us whether this behavior is intended.}
Here the Scala compiler does detect two possible instances for |Int => Int|,
but does not select the most specific one. 
Rejecting line~(6) has another unfortunate consequence: not only is the
semantics not preserved under unfolding, but typing is not preserved either!
Clearly preserving desirable properties such as coherence and type preservation is 
a subtle matter in the presence of implicits and deserves careful study. 

\subsection{An Overview of $\ourlang$}\label{sec:overview:ourlang}

Like Haskell $\ourlang$ requires coherence and
like Scala it permits nested declarations, and does not guarantee global uniqueness.
$\ourlang$ improves upon 
the implicit calculus~\cite{oliveira12implicit}, which is an incoherent calculus 
designed to model the essence of Scala implicits. Like the implicit
calculus it combines standard scoping mechanisms (abstractions and
applications) and types \`a la System~F, with a
logic-programming-style query language.
We now present the key features of $\ourlang$ and how
these features are used for IP.

\paragraph{Fetching Values by Type} A central construct in
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

\paragraph{Constructing Values with Type-Directed Rules} $\ourlang$ constructs values with 
type-directed rules (similar to functions) defined by the programmer. A rule (or rule
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

The type of the rule above is |Int => Int|. This type denotes that the rule has type |Int| provided 
a value of type |Int| is available in the implicit environment. 
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

\begin{comment}
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

< implicit 1 in implicit True in ((query Int) + 1, not (query Bool))

\noindent which returns |(2,False)|.
\end{comment} 

\paragraph{Higher-Order Rules} $\ourlang$ supports higher-order
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

< implicit 3 in implicit (rule Int (((query Int), (query Int) + 1))) in query (Pair Int Int)

Note that higher-order rules are a feature introduced by the implicit calculus and 
are neither supported in Haskell nor Scala.

\paragraph{Recursive Resolution} 
Note that resolving the  query |(query (Pair Int Int))| above
involves applying multiple rules. 
%combining multiple rules. 
The current environment does not contain
the required integer pair. It does however contain the integer $3$ and a rule 
%$\qlam{\tyInt}{\texttt{(\qask{\tyInt},\qask{\tyInt}+1)}}$
|rule (Int => Pair Int Int) (((query Int), (query Int) + 1))| to compute a
pair from an integer. Hence, the query is resolved with $(3,4)$, the
result of applying the pair-producing rule to $3$.


%format biglam a n = "\Lambda " a ". " n 
%format dots = "\ldots"

\paragraph{Polymorphic Rules and Queries} $\ourlang$ allows polymorphic rules. For example, the rule 
|biglam a (rule a (((query a),(query a))))|
abstracts over a type using standard type abstraction and then uses 
a rule abstraction to provide a value of type |a| in the implicit environment of 
the rule body. This rule has type |forall a . a => Pair a a|
and can be instantiated to multiple rules of monomorphic types
%%\[
%%\rulety{\tyint}{\tyint\times\tyint}, 
%%\rulety{\tybool}{\tybool\times\tybool}, \cdots.
%%\]
|Int => Pair Int Int, Bool => Pair Bool Bool, dots|.

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

> implicit 3 in implicit True in implicit (biglam a (rule a (((query a),(query a))))) in
>   (query (Pair Int Int), query (Pair Bool Bool))

\paragraph{Combining Higher-Order and Polymorphic Rules} 
We can build a pair of integer pairs with the 
rule | rule Int (rule ((forall a . a => Pair a a)) (((query (Pair (Pair Int Int) (Pair Int Int))))))|.
It proceeds by applying the rule of type
|forall a . a => Pair a a| 
twice in a row: first to an integer, and again to the result (an
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

> implicit 3 in implicit (biglam a (rule a (((query a),(query a))))) in (query (Pair (Pair Int Int) (Pair Int Int)))

%%rule (forall a . {a} => Pair a a) (((query a),(query a)))} in


% The $(3,3)$ pair is from applying the rule 
% %% $\qLam{\alpha}{\qlam{\alpha}{(\qask{\alpha},\qask{\alpha})}}$
% |rule (forall a . {a} => Pair a a) (((query a),(query a)))|
% to $3$, and the final answer $((3,3),(3,3))$ from applying the same
% rule to $(3,3)$.

\paragraph{Locally and Lexically Scoped Rules} 
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

\subsection{Overlapping Rules and Coherence in $\ourlang$}
\label{sec:overview:incoherence}

As the previous example shows, the lexical scope imposes a natural precedence
on rules. This precedence means that the lexically nearest rule is used to
resolve a query, and not necessarily the most specific rule.
For instance, the following $\ourlang$ variation on the running |trans|
example from Section~\ref{sec:overview-coherence}

> implicit (fun (n) (n + 1) : Int -> Int)  in 
>    implicit (fun (x) (x) : forall a. a -> a)  in 
>       query (Int -> Int) 3

yields the result |3| as the inner identity rule has precedence over the
more specific incrementation rule in the outer scope. Yet, this lexical
precedence alone is insufficient to guarantee coherence.
Consider the program

> let bad : forall b.b -> b =
>   implicit (fun (x) (x) : forall a. a -> a) in
>      implicit (fun (n) (n + 1) : Int -> Int) in 
>       query (b -> b)
> in bad Int 3

While the query |query (b -> b)| always matches |forall a. a -> a|, that is not
always the lexically nearest match. Indeed, if |b| is instantiated to
|Int| the rule |Int -> Int| is a nearer match. However, if |b| is
instantiated to any other type, |Int -> Int| is not a valid match. In summary,
we cannot always statically determine the lexically nearest match. 

One might consider to resolve the incoherence by picking the lexically nearest
rule that matches all possible instantiations of the query, e.g., |forall
a. a -> a| in the example. While this poses no threat to type soundness, this
form of incoherence is nevertheless undesirable for two reasons.
Firstly, it makes the behaviour of programs harder to predict, and, secondly,
the behaviour of programs is not stable under inlining. Indeed, if we inline the
function definition of |bad| at the call site and substitute the arguments, we obtain the specialised program

> implicit (fun (x) (x) : forall a. a -> a) in
>    implicit (fun (n) (n + 1) : Int -> Int) in 
>     query (Int -> Int) 3

This program yields the result |4| while the original incoherent version would yield |3|.
To avoid this unpredictable behaviour, $\ourlang$ rejects incoherent programs.

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

The \emph{coherence} principle states under what conditions the behaviour of
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

  The coherence principle states under what conditions the behaviour of
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

% \subsection{Runtime Errors and Coherence Failures}
% \label{subsec:error}
% In $\ourlang$, ill-behaved programs either raise runtime errors or are
% incoherent. The principal source of runtime errors is query failure,
% which is caused by either lookup failure or ambiguous instantiation
% during resolution. Coherence failure happens when a query in a
% program does not have a single nearest match or its single nearest
% match is not the one used at runtime.
% 
% \paragraph{Lookup Failures}
% A lookup fails if there is no matching rule in the rule environment,
% or there are multiple matching rules.
% 
% The first cause, no matching rule, is the simplest, illustrated by the
% following two examples:
% \[\begin{array}{rl}
% \myset{} &\turns  |query Int| \\
% \myset{|{Bool} => Int : -|}& \turns |query Int|
% \end{array}
% \noindent \]
% In the first example, resolution does not find a matching rule for the
% given |Int| type in the environment. In the second example,
% resolution finds a matching rule for |Int| in the first step, but
% does not find one in the recursive step for |Bool|.
% 
% The second cause are multiple matching rules, which is the case in the
% following two examples:
% 
% > {Int : 1, Int : 2} turns (query Int)
% > {forall a.a -> Int : -, forall a.Int -> a : - } turns (query (Int -> Int))
% \noindent
% 
% In the first example, two different rules produce a value for the same
% type |Int|; arbitrarily choosing one of 1 and 2
% makes the program's behavior unpredictable. To avoid this ambiguity,
% the lookup fails instead. The second example shows that two rules can
% be used to produce a value of the same type, even though the rule
% types are different. The two polymorphic rule types can be instantiated to the
% same type, in this case to |Int -> Int|.
% 
% \paragraph{Ambiguous Instantiations}
% In some cases, resolution does not determine how to instantiate a
% fetched rule. Consider the following example:\footnote{$\rclos{n}$
%   denotes a closure value; distinct numbers mean distinct values.}\[
% \begin{array}{rl}
%   \myset{\quad 
%     |forall a.{a -> a} => Int : rclos 1| &, \\
%     |Bool -> Bool : rclos 2|&, \\
%     |forall b. b -> b : rclos 3|&} \turns |query Int|
% \end{array}\]
% % > { forall a. {a -> a} => Int : (rclos 1), Int -> Int : (rclos 2),
% % >  Bool -> Bool : (rclos 3) } turns (query Int)
% The |query Int| matches the first rule without determining an
% instantiation for |a|. However, the runtime behavior could actually
% depend on the choice between |rclos 2| and |rclos 3|. Thus the query
% is ambiguous.
% 
% \paragraph{Coherence Failures}
% A program is coherent iff every query in the program has a single,
% lexically nearest match, which is the same statically and at runtime. This
% means that all the runtime queries instantiated from the original
% query should have the same resolution result. Consider the following
% example:
% 
% > let f : forall b.b -> b =
% >   implicit {fun (x) (x) : forall a. a -> a} in
% >       query (b -> b)
% \noindent
% This program is coherent because no matter which type the type
% variable |b| will have at runtime, the resolution results for all
% those queries are the same (|forall a. a -> a|). However, the following program is
% incoherent:
% 
% > let f : forall b.b -> b =
% >   implicit {fun (x) (x) : forall a. a -> a} in
% >      implicit {fun (n) (n + 1) : Int -> Int} in 
% >       query (b -> b)
% \noindent
% There are two possible results for the query |query (b -> b)|
% depending on the type of |b| at runtime. If the query is instantiated
% by the substitution $\subst{|b|}{|Int|}$, then the nearest result is
% |Int -> Int| and otherwise, |forall a. a -> a| is the one.
% 
% Our static type system will safely reject such programs that can have
% the aforementioned runtime errors or coherence failures.
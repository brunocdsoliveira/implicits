%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Rule.fmt
%%include Scala.fmt
%format new = "\bf{new}"

%format === = "\cong"

\section{Overview}
\label{sec:overview}

This section summarises the relevant background on type classes, IP 
and coherence, and introduces the key features of $\ourlang$.
We first discuss Haskell type classes, the oldest
and most well-established IP mechanism, then compare them to
Scala implicits, and finally we introduce the approach taken in $\ourlang$.

%-------------------------------------------------------------------------------
\subsection{Type Classes and Implicit Programming}\label{subsec:tclasses}

Type classes enable the declaration of overloaded functions like comparison.

> class Ord a where
>   (<=) :: a -> a -> Bool

A type class declaration consists of: a class name, such as |Ord|; a type
parameter, such as |a|; and a set of method declarations,
such as |(<=)|. Each of
the methods in the type class declaration should have at least one
occurrence of the type parameter |a| in their signature.
% (either as an argument or as a return type).
% The type parameter may be neither an argument nor a return type,
% as in showList :: [a] -> String.

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
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
>   (x,x') <= (y,y') = x <= y && (not (y <= x) || x' <= y')

\noindent The first two instances provide the implementation of ordering for integers
and characters, in terms of primitive functions.
The third instance is more interesting, and provides the
implementation of lexicographic ordering for pairs. In this case, the ordering
instance itself \emph{requires} an ordering instance for both
components of the pair. These requirements are resolved 
by the compiler using the existing set of instances in a process called 
\emph{resolution}.  
Using |Ord| we can define a generic sorting function

> sort :: Ord a => [a] -> [a]

\noindent that takes a list of elements of an arbitrary type |a| and
returns a list of the same type, as long as ordering is supported
for type |a|\footnote{Note that, in Haskell, the single arrow (|->|) denotes a 
function type constructor, whereas the double arrow (|=>|) denotes a type with 
type class constraints (on the left of the arrow). In the |sort| function, for example, 
|Ord a| are the constraints.}.

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
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

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
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

%-------------------------------------------------------------------------------
\subsection{Coherence in Type Classes}
\label{sec:overview-coherence}

An IP design is \emph{coherent} if
any valid program has exactly one meaning (that is,
the semantics is not ambiguous). 
Haskell imposes restrictions to guarantee
coherence. For example, Haskell rejects the expression:

> show (read "3") == "3" 

\noindent due to \emph{ambiguity} of 
\emph{type class resolution}~\cite{qual}. The functions |show| and
|read| print and parse values of any type |a| that implements 
the classes |Show| and |Read|:  

> class Show a where
>   show :: a -> String
> class Read a where
>   read :: String -> a

The program is rejected because
there is more that one possible choice for |a|. For example
|a| can be instantiated to |Int|, |Float|, or |Char|. 
Choosing |a=Float| leads to |False|,
since showing the float |3| would result in |"3.0"|,
while choosing |a=Int| leads to |True|. In other words if this 
expression was accepted then it could have multiple possible semantics. 
To ensure coherence instead of making an arbitrary choice Haskell rejects such programs.

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Overlapping Instances} 
Advanced features of type classes, such as overlapping
instances, require additional restrictions to
ensure coherence. The following program illustrates some of the issues:

> class Trans a where trans :: a -> a
> instance Trans a where trans x = x
> instance Trans Int where trans x = x+1

\noindent This program declares a type class |Trans a| for defining
transformations on some type |a|. The first instance provides a default
implementation for any type, the identity transformation. The second instance
defines a transformation for integers only. 

An important question here is what happens if 
we write an expression like |trans 3|. Shall we pick the first 
or the second instance? Ideally this question should be answered 
by the language specification. One possible choice for the 
specification (not the Haskell choice) 
would be to allow any matching instance to be used, but 
this choice would lead to incoherence, since |trans 3| could 
then both evaluate to |3| or |4|. Instead, for overlapping instances, 
the GHC documentation~\cite{overlapping_instances}
%\footnote{\url{http://ghc.readthedocs.io/en/8.0.1/glasgow_exts.html##overlapping-instances}}
makes a different choice and 
declares that the \emph{most specific instance} should be chosen. 
For the expression |trans 3|, the most specific is |Trans Int| 
and the expression evaluates to |4|. 

For the particular program |trans 3|, the Haskell specification manages to avoid 
incoherence by using the 
most specific instance, which ensures an unambiguous semantics. 
Thus Haskell preserves coherence in the presence of a certain kind of overlapping instances, 
but there are other problematic overlapping instances that threaten the coherence property.

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Incoherent Instances}
With overlapping instances it is not always the case that a most specific 
instance exists. Consider the following type class and instance declarations:

> class C a b where 
>   m :: a -> b -> Bool
>
> instance C Bool a where 
>   m x y = x
>
> instance C a Bool where
>   m x y = y

\noindent If we write the following program 

> incoherent = m True False -- rejected without IncoherentInstances extension

\noindent then there is no most specific instance: both instances are equally specific.
In this case, even with the overlapping instances extension activated, Haskell rejects 
the program. 

However Haskell also supports one additional extension, called \texttt{IncoherentInstances}, 
for allowing a more general kind of overlapping instances. With
\texttt{IncoherentInstances} activated, Haskell accepts the |incoherent| definition. 
The (informal) language specification~\cite{overlapping_instances}
%\footnote{\url{http://ghc.readthedocs.io/en/8.0.1/glasgow_exts.html##overlapping-instances}}
for \texttt{IncoherentInstances}
 essentially says that in such a situation any matching instance could be picked. 
Thus either of the two instances above can be picked, resulting in different 
evaluation results for the expression. Thus, as the name indicates, the 
expression |incoherent| leads to incoherence.


\begin{comment}
The overlapping declarations can be incoherent 
since it is unclear whether |trans 3| should return
|3| using the first instance, or |4| using the second instance.
Because the second instance is more specific, one 
might expect that it supersedes the first one; and that is indeed how
Haskell assigns a meaning to overlapping instances when they are permitted.
\end{comment}

%-------------------------------------------------------------------------------
\subsection{Stability in Type Classes}

Another important property that is closely related to coherence is \emph{stability}. 
Informally stability ensures that instantiation of type variables does not affect resolution. 
Unfortunately overlapping instances threaten this property. 
Consider the following declaration, that uses the |trans| method from the type 
class |Trans| and the two instances declared previously:

> bad :: a -> a
> bad x = trans x  -- unstable definition!

Note here that the type of |bad| is |a -> a| instead of |Trans a => a -> a|. 
In Haskell both signatures can be accepted, but they are not equivalent. 
With |Trans a => a -> a| resolution is deferred to the call site of bad, allowing the instance of |Trans a| to be selected when |a| has been instantiated to a (potentially) more precise type.
%With |Trans a => a -> a|
%resolution is applied lazily. That is, resolution is delayed to the calls of |bad|, allowing 
%the instance of |Trans a| to be selected when more static information is available. 
By contrast, with |a -> a| resolution is applied eagerly, and an instance must 
be selected at the definition site. 
If Haskell were to accept this definition, it
would have to implement |trans| using the first instance,
since |trans| is applied at the arbitrary type |a|.
Unfortunately this would mean that |bad 3| returns |3| but |trans 3| returns |4|,
even though |bad| and |trans| are defined to be
equal, a nasty impediment to equational reasoning!

For this reason Haskell rejects the program by default. A programmer who really
wants such behaviour can enable the \texttt{IncoherentInstances} compiler flag,
which allows the program to type check. 

Note that even though to allow |bad| we need the
\texttt{IncoherentInstances} extension, which is suggestive of the
definition breaking \emph{coherence}, the issue here is not really
coherence but rather stability. That is, type instantiation affects type class instantiation.  As this example illustrates, instability is
actually observable from a compiler implementation like GHC: we can
observe that |bad 3| and |trans 3| behave differently. In contrast
(in)coherence is not really observable from a compiler implementation:
we need a language specification to understand whether there is
incoherence or not.

The \texttt{IncoherentInstances} extension is understood to be highly problematic 
among Haskell programmers, since it can break both stability and coherence. 
Thus its use is greatly discouraged. 

%-------------------------------------------------------------------------------
\subsection{Global Uniqueness in Type Classes} A consequence 
of having at most one instance of a type class 
per type in a program is \emph{global uniqueness} of instances~\cite{uniqueness}. That is, 
at any point in the program type class resolution for a particular 
type always resolves to the same value. Global uniqueness is a simple way to guarantee coherence, but 
it offers more than just coherence.
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
various circumstances\footnote{\url{http://stackoverflow.com/questions/12735274/breaking-data-set-integrity-without-generalizednewtypederiving}}.
In fact, it is acknowledged that providing a global uniqueness check is quite 
challenging for Haskell implementations.\footnote{\url{https://mail.haskell.org/pipermail/haskell-cafe/2012-October/103887.html}}

%-------------------------------------------------------------------------------
\subsection{Scala Implicits and Stability}

Scala implicits~\cite{implicits} are an interesting alternative IP
design. Unlike type classes, implicits are locally scoped.
Consequently Scala does not have the global uniqueness
property, since different ``instances'' may exist for
the same type in different scopes. Another interesting difference
between implicits and type classes is that values of any type can be
used as implicit parameters, and there are no special constructs analogous
to type class or instance declarations. Instead, implicits are modelled
with ordinary types. They can be abstracted over and do not suffer
from the second-class nature of type classes. These features mean that 
Scala implicits have a wider range of applications than type classes.
Unlike Haskell type classes, however, with Scala implicits there is no way to 
enforce stability. 

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Modelling Type Classes with Implicits}
In Scala there is no special construct for defining the interface of 
a type class. Instead we can use regular interfaces to model 
type class interfaces. Scala models OO interfaces with traits~\cite{Scharli03traits}.
For example, the 3 interfaces presented in Section~\ref{subsec:tclasses} can 
be modelled as:

< trait Ord[T] {def le(x:T,y:T) : Boolean}
< trait Show[T] {def show (x : T) : String}
< trait Read[T] {def read (x : String) : T}

\noindent Of course, by declaring traits like this, we still require 
explicit objects to call the methods on. To be able to use 
methods in the same way as Haskell type classes, the object (or dictionary) 
should be passed implicitly. This can be achieved by using Scala's
implicits feature:

%{
%format . = "."

< def cmp[A](x:A,y:A)(implicit ordD : Ord[A]):Boolean = ordD.le(x,y)

%}

\noindent The Scala definition of |cmp| plays the same role as |<=| in
Haskell. The type of |cmp| states that |cmp| is parametrized in a
type |A|, takes two (explicit) arguments of type |A|, and one 
implicit parameter (|ordD|). This is similar to a Haskell 
signature |Ord a => a -> a -> Bool|, except that the implicit argument 
comes last. Additionally, unlike Haskell, at call sites it is 
possible to pass the implicit argument explicitly, if desired. 

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Context Bounds and Queries} For the purposes of this paper we will, 
however, present |cmp| using \emph{context bounds}: 
an alternative way to declare functions with constraints (or implicit arguments), supported in Scala. Context bounds are a simple syntactic sugar built 
on top of implicit parameters.
Using context bounds, the |cmp| definition can be rewritten 
into:

%{
%format . = "."

< def cmp[A:Ord](x:A,y:A):Boolean = ?[Ord[A]].le(x,y)

%}

\noindent The notation |A:Ord| is the so-called context bound. 
This notation enables us to
declare a constraint on the type |A|. Namely, the type |A| should be
an ``instance'' of |Ord[A]|. In the background the Scala compiler rewrites 
definitions with context bounds into definitions with implicit arguments. 
In the body of |cmp| an additional mechanism, called an
implicit \emph{query}, is now necessary to query the environment for a
value of type |Ord[A]|. This query mechanism in Scala is nothing more 
than a simple function taking an implicit argument. The (slightly simplified)
definition of the query operator is:\footnote{In Scala the operator is known by the longer name \texttt{implicitly}.}

< def ?[T] (implicit w:T):T = w    

\noindent 
The operator |?| takes a single \emph{implicit} argument of type |T| and returns that value. 
Hence operationally it is just the identity function. The key point is that, when used, 
the implicit argument is filled in automatically by the compiler. In the definition 
of |cmp|, the expression |?[Ord[A]]| triggers the compiler to look for a value 
of type |Ord[A]| in the \emph{implicit 
environment}. The implicit environment collects values that are declared to be implicit, 
and usable for automatic implicit resolution. 

Implicit values, which correspond to type class instances in Haskell, 
are declared by using the |implicit| keyword. The following three examples capture
the ``instances'' for |Ord|:  
%{
%format . = "."


  
< implicit val OrdInt = new Ord[Int] {
<    def le(x : Int, y: Int) = primIntLe(x,y)
< }
<
< implicit val OrdChar = new Ord[Char] {
<   def le(x : Char, y: Char) = primCharLe(x,y)
< }
< 
< implicit def OrdPair[A : Ord, B : Ord] = new Ord[(A,B)] {
<   def le(x : (A,B), y : (A,B)) = 
<      cmp(fst(x),fst(y)) && (!(cmp(fst(y),fst(x))) || cmp(snd(x),snd(y)))
< }

%}

With those definitions it is now possible to declare functions, such 
as |sort|, that require |Ord| instances:
 
< def sort[A : Ord](x : List[A]) = ...

\noindent This Scala |sort| function can be used in a similar way to the corresponding Haskell function. 
For example the call |sort (List((3,'a'), (2,'c'), (3,'b')))| is valid and does not 
require an explicit argument of type |Ord[(Int,Char)]|. Instead this argument is computed 
from the implicit definitions for |Ord|.

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Wider Range of Applications for Implicits} Scala implicits do allow for 
a wider range of applications than type classes.
One example where implicits naturally address a problem that type classes 
do not address well is the problem of 
\emph{implicit configurations}~\cite{Kiselyov04}. The following 
example, adapted from Kiselyov and Shan, illustrates this:

\begin{code}
def add(x : Int, y : Int)(implicit modulus : Int) = (x + y) % modulus  
def mul(x : Int, y : Int)(implicit modulus : Int) = (x * y) % modulus  
implicit val defMod : Int = 4       
def test = add(mul(3,3), mul(5,5)) // returns 2
\end{code}

\noindent Here the idea is to model \emph{modular arithmetic}, 
where numbers
that differ by multiples of a 
given modulus are treated as identical.
For example 3 * 3 = 1 (mod 4) because 9 and 1 differ 
by a multiple of 4. The code shows the definition of 
addition and multiplication in modular arithmetic, where
in Scala |%| is modulo division. Both addition and multiplication 
include a third (implicit) parameter, which is the modulus 
of the division. Although the modulus could be passed explicitly 
this would be extremely cumbersome. Instead it is desirable that 
the modulus is passed implicitly. Scala implicits allow this, by simply marking 
the |modulus| parameter in |add| and |mul| with the |implicit| keyword. 
The third line shows how to set up an implicit value for the modulus. 
Adding |implicit| before |val| signals that the value being defined 
is available for synthesising values of type |Int|. 
Finally, |test| illustrates how expressions doing modular arithmetic 
can be defined using the implicit modulus. Because Scala also 
has local scoping, different modulus values can be used in
different scopes.

Several other examples of applications that can be covered by
implicits, but are harder to achieve with type classes are found in
the existing literature~\cite{implicits,oliveira12implicit,odersky17implicits}. In
particular, in a recent paper Odersky et al. \shortcite{odersky17implicits} introduce \emph{implicit
function types}, which are a generalization
of the original Scala implicits~\cite{implicits}, and demonstrate
several interesting use cases for implicits.

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Instability in Scala}
Although Scala allows \emph{nested} local scoping and overlapping implicits,
\textit{stability} is not guaranteed. Figure~\ref{fig:scala} illustrates
the issue briefly, based on the example from Section~\ref{sec:overview-coherence}.
Line~(1) defines a function |id| with type parameter |a|, which is simply
the identity function of type |a => a|\footnote{Note that the |a => b| notation 
in Scala represents a function type, rather than a rule type.}.  
The |implicit| keyword in the declaration specifies that this value may
be used to synthesise an implicit argument.
Line~(2) defines a function |trans| with type parameter |a|,
which takes an implicit argument |f| of type |a => a| and returns $f(x)$.
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
   def bad[a](x:a) : a = trans[a](x)		   // (4) unstable definition!
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
Interestingly the expression in line~(6), which is accepted in Haskell, is actually rejected in Scala. Note that the expression in line~(6) is simply the unfolding of the expression 
in line~(5) (which is accepted in Scala).
In the expression in line~(6) the Scala compiler does detect two possible instances for |Int => Int|,
but does not select the most specific one. In this case the call in line~(6) is considered 
ambiguous because Scala accounts for other factors, when deciding where there is ambiguity 
or not~\cite{implicits,odersky17implicits}.
%%The reason for this is that 
%%Scala uses a tie-breaker rule for disambiguating instances. Scala attributes
%%1 point to a rule in the following situations: a) a rule is in a deeper scope than the other rule; 
%%b) a rule has a more specific type than another rule~\footnote{There are other rules, 
%%but they can be ignored for this example}. In this case there's a draw, since the 
%%definition of |trans| gets one point from being in a de, and the rule |trans|  
Rejecting line~(6) has another unfortunate consequence. Not only is the
semantics not preserved under unfolding, but typing is not preserved either: i.e. 
going from line~(5) to line~(6) using a simple unfolding step makes the program ill-typed!
Clearly preserving desirable properties such as stability and type preservation is 
a subtle matter in the presence of implicits and deserves careful study. 

%-------------------------------------------------------------------------------
\subsection{An Overview of $\ourlang$}\label{sec:overview:ourlang}

Like Haskell, our calculus $\ourlang$ guarantees stability and coherence and, like Scala, it permits
nested/overlapping declarations, and does not guarantee global
uniqueness. $\ourlang$ improves upon the implicit
calculus~\cite{oliveira12implicit} by having stability and a better,
more expressive design for resolution. Like the implicit calculus, the
primary goal of $\ourlang$ is to model \emph{implicit resolution} and
the \emph{scoping} of implicit values used by resolution. 
Next we iterate 
over the key constructs and features of $\ourlang$.

\begin{comment}
An important remark is that $\ourlang$, like the implicit calculus, is
designed as a \emph{core calculus}, and therefore provides no
type-inference. As a result programs written in $\ourlang$ still require
many type annotations. The primary goal of $\ourlang$ is to model
\emph{implicit resolution} as well as the scoping of implicit values.
Some work on type-inference can be found in implicit calculus
paper~\cite{}, and also in a recent paper by Odersky et al.~\cite{}.
A full approach to type-inference that allows designing 
source languages with implicit polymorphism is left for future work.
\end{comment}

\begin{comment}
\begin{itemize}

\item {\bf Queries:} $\ourlang$ models the concept of an \emph{implicit query}, which is 
also used in Scala to trigger implicit resolution.

\item {\bf Resolution:} Queries are resolved by a mechanism called \emph{resolution}. Resolution 
uses a set of rules  

\item {\bf Rules:} 

\item {bf 

\end{itemize}
\end{comment}


%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Fetching Values by Type} A central construct in
$\ourlang$ is a query. Queries allow values to be fetched by type, not by name.  
  For example, in the following function call

< foo (query Int)
 
the query |query Int| looks up a value of type |Int| in the implicit
environment, to serve as an actual argument. Note that queries in $\ourlang$
play exactly the same role as the operator |?| in Scala. 


%%Function \texttt{inc} is applied to an argument (we call ``implicit
%%query'') that queries ``$\qask{\tyInt}$'' by mentioning just its
%%type \tyInt.  The int-typed entry in the current implicit
%%environment is looked up  to provide an integer value. 

%%In practice, the implicit query ``$\qask{\tyInt}$'' can even be
%%omitted thanks to type inference. Our calculus makes implicit queries
%%always manifest in text. 

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Constructing Values with Type-Directed Rules} $\ourlang$ constructs values, using
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

The type of the rule above is the \emph{rule type} |Int => Int|. 
This type denotes that the rule has type |Int| provided 
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

The analog to rule abstractions in Scala are functions with arguments marked 
with the |implicit| keyword. However, in older versions of Scala, 
functions with implicit arguments were not first class and could not be abstracted 
over. 
In particular in older versions of Scala it was impossible 
to express the type of a function with an implicit argument.
Recent versions of Scala, partly inspired by the implicit calculus, 
generalize the mechanism of implicits and make rule abstractions and types 
first class too, by what they call \emph{implicit function types}~\cite{odersky17implicits}.

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

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
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

% < implicit 3 in implicit (rule Int (((query Int), (query Int) + 1))) in query (Pair Int Int)

> (rule Int (rule ((Int => Pair Int Int)) (query (Pair Int Int)))) 
>    with 3 
>    with (rule Int (((query Int), (query Int) + 1)))

%%Note that higher-order rules are a feature introduced by the implicit calculus and 
%%are neither supported in Haskell nor Scala.

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Recursive Resolution} 
Note that resolving the  query |(query (Pair Int Int))| above
involves multiple implicits. 
The current environment does not contain
the required integer pair. It does however contain the integer $3$ and a rule 
%$\qlam{\tyInt}{\texttt{(\qask{\tyInt},\qask{\tyInt}+1)}}$
|rule (Int) (((query Int), (query Int) + 1))| to compute a
pair from an integer. Hence, the query is resolved with $(3,4)$, the
result of applying the pair-producing rule to $3$.


%format biglam a n = "\Lambda " a ". " n 
%format dots = "\ldots"

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Polymorphic Implicits and Queries} $\ourlang$ features explicit polymorphism. For example, the rule 
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
polymorphic rule. The following expression returns 
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

> implicit 3 in implicit True in implicit (biglam a (rule a (((query a),(query a))))) in (query (Pair Int Int), query (Pair Bool Bool))

Queries can be polymorphic too. For instance, the following example extracts the polymorphic
implicit with a polymorphic query. 

> implicit (biglam a (rule a (((query a),(query a))))) in query (forall b. b => (Pair b b)))

In practice, polymorphic queries are useful in combination with higher-kinded
types where they occur as recursive resolvents of polymorphic rules. We cannot
illustrate this with \name as, to keep its definition small, it is not equipped with higher-kinded types. The
interested reader can find examples in the work of Bottu et al.~\shortcite{haskell2017b}.


%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Combining Higher-Order and Polymorphic Rules} 
The rule: 

< rule Int (rule ((forall a . a => Pair a a)) (((query (Pair (Pair Int Int) (Pair Int Int))))))

prescribes how to build a pair of integer pairs, inductively from an
integer value, by consecutively applying the rule of type
|forall a . a => Pair a a| 
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

> implicit 3 in implicit (biglam a (rule a (((query a),(query a))))) in (query (Pair (Pair Int Int) (Pair Int Int)))

%%rule (forall a . {a} => Pair a a) (((query a),(query a)))} in


% The $(3,3)$ pair is from applying the rule 
% %% $\qLam{\alpha}{\qlam{\alpha}{(\qask{\alpha},\qask{\alpha})}}$
% |rule (forall a . {a} => Pair a a) (((query a),(query a)))|
% to $3$, and the final answer $((3,3),(3,3))$ from applying the same
% rule to $(3,3)$.

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\paragraph{Locally and Lexically Scoped Implicits} 
Implicits can be nested and resolution respects their lexical scope. 
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

\paragraph{Care with reduction}

Observe that some care is required with reduction. Consider the following program.

> implicit 1: Int  in
>    let x = ?Int     in
>      implicit 2: Int  in
>        x

Naively,  one might expect it to reduce to the following. 

> implicit 1: Int  in
>   implicit 2: Int  in
>     ?Int

But this would change its meaning: the first program returns 1, while the second returns 2.
The solution is to never consider a term as a candidate for substitution until all of its implicits
have been resolved. This is similar to restrictions encountered elsewhere, for instance not
allowing export of a function from a module that mentions a type class if the module introduces
a local instance of that type class~\cite{?}.\bruno{TODO: Find reference?}\bruno{Also I am 
not entirely happy about the paragraph. I think we need to qualify reduction here, we are probably talking 
about full reduction (applying reduction at arbitrary points in the program), 
because with call-by-value or call-by-name reduction there is no issue at all.}

%~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ ~ 
\subsubsection{Encoding Simple Type Classes in $\ourlang$}\label{subsec:encoding}
A simple form of type classes can be encoded in $\ourlang$ similarly 
to how type classes can be encoded in Scala. In this section we briefly 
(and informally) illustrate the encoding using examples. 
The simple encoding presented here does not deal with \emph{superclasses}. 
We discuss superclasses 
in Section~\ref{sec:discussion}.
\begin{comment} 
However it is known that superclasses can be modelled as sugar, by computing a 
transitive closure of the superclasses~\cite{}. Indeed in recent work 
Bottu et al.~\cite{}, has shown how to take some of the key ideas of $\ourlang$ 
to model an 
\end{comment}

Next we illustrate how the encoding works on the examples
from Section~\ref{subsec:tclasses}. To help with readability we assume a few
convenient source language features not available in $\ourlang$ (which is
designed as a formal core calculus rather than a full-fledged source language). 
In particular $\ourlang$ has no type-inference and requires explicit
rule applications and queries. The design of a source language that supports
type-inference, implicit rule applications, implicit polymorphism and that 
translates into a $\ourlang$-like calculus was already explored in our previous work on the implicit
calculus~\cite{oliveira12implicit}. To better illustrate some of our examples
here we will assume such source language features.  
 
Firstly we use type synonyms to allow us to give a short name to a type.
Secondly we use records. Using both of those constructs, the three type classes
introduced in Sections~\ref{subsec:tclasses} and \ref{sec:overview-coherence}
can be declared as:

< type Ord a = {le : a -> a -> Bool}
< type Show a = {show : a -> String}
< type Read a = {read : String -> a}

Similarly to the Scala encoding we define a |cmp| function, 
that makes the argument of type |Ord a| implicit: 

%{

%format . = "."

< let cmp : forall a . Ord a => a -> a -> Bool = (? : Ord a).le in

%}

Here the query is annotated with a type |Ord a| triggering the 
resolution of a value of that type. Once that value is computed, the 
field |le| can be extracted from it. 
   
The ``instances'' of |Ord| can be defined as record values or 
rule types returning an |Ord| record.

%{
%format . = ".~"

< let ordInt : Ord Int = {le = \x . \y . primIntLe x y} in
< let ordChar : Ord Char = {le = \x . \y . primCharLe x y} in
< let ordPair : forall a b. Ord a => Ord b => Ord (a,b) = {le = \x . \y . 
<    cmp (fst x) (fst y) && ((not (cmp (fst y) (fst x))) || cmp (snd x) (snd y))} in

%}

\noindent Here the first two values denote instances for the base types 
|Int| and |Char|. The instance for pairs (|ordPair|) has two constraints (|Ord a| 
and |Ord b|), and those constraints are implicitly used by |cmp|. 

Given a |sort| function: 

< let sort : forall a . Ord a => List a -> List a = ... 

\noindent it now is possible to use |implicit| to introduce 
the ``instances'' into the implicit scope and have the |Ord (List Int)|
argument of the call |sort [(3,'a'), (2,'c'), (3,'b')]| automatically inferred:

< implicit ordInt in 
<   implicit ordChar in
<      implicit ordPair in
<        sort [(3,'a'), (2,'c'), (3,'b')]

%-------------------------------------------------------------------------------
\subsection{Overlapping Implicits and Stability in $\ourlang$}
\label{sec:overview:incoherence}

As previously shown, the lexical scope imposes a natural precedence
on implicits that ensures coherence. This precedence means that the lexically
nearest implicit is used to resolve a query, and not necessarily the most specific
implicit.  For instance, the following $\ourlang$ variation on the running |trans|
example from Section~\ref{sec:overview-coherence}

> implicit (fun (n) (n + 1) : Int -> Int)  in 
>    implicit (fun (x) (x) : forall a. a -> a)  in 
>       query (Int -> Int) 3

yields the result |3| as the inner identity implicit has precedence over the
more specific incrementation implicit in the outer scope. Yet, it is not always
possible to statically select the nearest matching implicit.
Consider the program fragment

> let bad : forall b.b -> b =
>   implicit (fun (x) (x) : forall a. a -> a) in
>      implicit (fun (n) (n + 1) : Int -> Int) in 
>       query (b -> b)

Here we cannot statically decide whether |Int -> Int| matches |b -> b|: it
depends on whether |b| is instantiated to |Int| or not.

One might consider to force the matter by picking the lexically
nearest implicit that matches all possible instantiations of the query, e.g.,
|forall a. a -> a| in the example. While this poses no threat to type
soundness, this approach is nevertheless undesirable for two reasons.
Firstly, it makes the behaviour of programs harder to predict, and, secondly,
the behaviour of programs is not \emph{stable under inlining}. Consider
the call |bad Int 3|, which would yield the result |3|. If instead we inline
the function definition of |bad| at the call site and
substitute the type argument, we obtain the specialised program

> implicit (fun (x) (x) : forall a. a -> a) in
>    implicit (fun (n) (n + 1) : Int -> Int) in 
>     query (Int -> Int) 3

Now |Int -> Int| is the nearest lexical match and the program yields the result
|4|. 
%Consequently, accepting such programs would imply that substituting equals for equals 
%does not work in general.
Consequently, inlining definitions changes their behavior.
To avoid this unpredictable behaviour, $\ourlang$ rejects such unstable
matchings. Technically speaking the key property that $\ourlang$ guarantees 
is \emph{stability of resolution} (see also Section~\ref{sec:trans}).
\begin{comment}
\begin{lemma}[Stability]
Resolution is stable under type substitution.
\[
\tenv,\alpha,\tenv' \ivturns \rulet \leadsto E \enskip\wedge\enskip \tenv \vdash \sigma
\enskip\Rightarrow\enskip 
\tenv,\tenv'[\sigma/\alpha] \ivturns \rulet[\sigma/\alpha] \leadsto E[|\sigma|/\alpha] \]
\end{lemma}
\end{comment}
Essentially this property ensures that type instantiation does not affect the
resolution of queries. That is, if some type variables appear free in a query
that resolves, then, after instantiating any or all of those type variables,
the query still resolves in the same way, i.e., using the same implicits. If it
cannot be statically guaranteed that resolution behaves in the same way for
\emph{every} instantiation, then the program is rejected. The benefit of
rejecting such potentially unstable programs is that the principle of
substituting equals for equals is not affected by the interaction between
resolution and instantiation. This makes reasoning about programs and code
refactoring more predictable.


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

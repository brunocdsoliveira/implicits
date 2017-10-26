%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Rule.fmt

\newcommand{\rhs}[1]{\mathit{rhs}(#1)}
\newcommand{\lhs}[1]{\mathit{lhs}(#1)}
\newcommand{\qtv}[1]{\mathit{qtv}(#1)}
\newcommand{\ftv}[1]{\mathit{ftv}(#1)}

\section{The $\name$ Calculus}
\label{sec:ourlang}

This section formalizes the syntax and type system of $\name$, while
Section~\ref{sec:trans} formalises the type-directed translation to System F.
To avoid duplication and ease reading, we present the type
system and type-directed translation together, using grey boxes to indicate
which parts of the rules belong to the type-directed translation. These
greyed parts can be ignored in this section and will be explained in the next.

%-------------------------------------------------------------------------------
\subsection{Syntax}    
\label{subsec:syntax}

Here is the syntax of the calculus:
\bda{llrl}
    \text{Types} & \rulet  & ::=  & \alpha \mid \rulet_1 \arrow \rulet_2 \mid \forall \alpha. \rulet \mid \rulet_1 \iarrow \rulet_2 \\
    \text{Expressions} & |e| & ::=  &
     x \mid \lambda (x:\rulet).e \mid e_1\,e_2 \mid \Lambda \alpha. e \mid e\,\rulet \mid \query \rulet \mid \ilambda \rulet. e \mid e_1 \with e_2  \\
\eda
%
%%endif
%
Types $\rulet$ comprise four constructs: type variables
$\alpha$; function types $\rulet_1 \arrow \rulet_2$; universal types
$\forall \alpha. \rulet$; and the novel \textit{rule} types $\rulet_1 \iarrow
\rulet_2$.  In a rule type $\rulet_1 \iarrow \rulet_2$, type $\rulet_1$ is
called the \textit{context} and type $\rulet_2$ the \textit{head}.

Expressions $e$ include three abstraction-elimination pairs.
Binder $\lambda (x:\rulet). e$ abstracts expression $e$ over values of type $\rulet$,
is eliminated by application $e_1\,e_2$, and refers to the bound value with variable $x$.
Binder $\Lambda \alpha.e$ abstracts expression $e$ over types, is eliminated
by type application $e\,\rulet$, and refers to the bound type with type variable $\alpha$ 
(but $\alpha$ itself is not a valid expression). Binder $\ilambda \rulet. e$ 
abstracts expression $e$ over implicit values of type $\rulet$, is eliminated by
implicit application $e_1 \with e_2$, and refers to the implicitly bound value with 
implicit query $\query \rulet$.
For convenience we adopt the Barendregt convention~\cite{barendregt}, that
variables in binders are distinct, throughout this article.
% Without loss of generality we assume that all variables $x$
% and type variables $\alpha$ in binders are distinct. If not, they
% can be easily renamed apart to be so.

Using rule abstractions and applications we can build the |implicit| 
sugar used in Section \ref{sec:overview}.
%{
%format == = "\defeq"
%format e1
\[ | implicit {-"\overline{"-} e : {-"\rulet}"-} in e1 == ({-" \overline{\lambda_? \rulet .} "-} e1) {-"\overline{"-} with e {-"}"-} | \]
%}\bruno{Also introduce let, which is used later, in the translation.}
Here $\overline{\lambda_? \rho .}$ is a shortform for 
$\lambda_? \rho_1.~\ldots~\lambda_? \rho_n.$, and
$\overline{|with|~e}$ is a shortform for
|with| $e_1 \ldots $ |with| $e_n$.

For brevity we have kept the $\name$ calculus small. Examples
may use additional syntax such as built-in integers, integer operators, and boolean
literals and types. 

%-------------------------------------------------------------------------------

\subsection{Type System}
\label{sec:types}

\figtwocol{fig:type}{Type System and Type-directed Translation to System F}{
\begin{center}
\framebox{\scriptsize
\begin{minipage}{.969\textwidth}
\bda{c}
\multicolumn{1}{c}{\myruleform{\tenv \turns \rulet}} \\ \\

  \myrule{WF-VarTy}
         { \alpha \in \tenv }
         { \tenv \turns \alpha } \quad\quad\quad
  \myrule{WF-FunTy}
         {\tenv \turns \rulet_1 \quad\quad \tenv \turns \rulet_2}
         {\tenv \turns \rulet_1 \arrow \rulet_2} \\ \\
  \myrule{WF-AbsTy}
         { \tenv, \alpha \turns \rulet}
         { \tenv \turns \forall\alpha.\rulet } \quad\quad\quad
  \myrule{WF-RulTy}
         {\tenv \turns \rulet_1 \quad\quad \tenv \turns \rulet_2}
         {\tenv \turns \rulet_1 \iarrow \rulet_2}
\eda

\bda{c} 

\multicolumn{1}{c}{
  \myruleform{\tenv \turns \relation{e}{\rulet}~\gbox{\leadsto E}}} \\
\\

\myrule{Ty-Var}
{ (\relation{x}{\rulet}) \in \tenv}
{ \tenv \turns \relation{x}{\rulet}~\gbox{\leadsto x}
} 
\\ \\

\myrule{Ty-Abs}
{ \tenv,\relation{x}{\rulet_1} \turns \relation{e}{\rulet_2}~\gbox{\leadsto E}
  \quad\quad\quad \tenv \turns \rulet_1 
}
{ \tenv \turns \relation{\lambda \relation{x}{\rulet_1}.e}{\rulet_1 \arrow \rulet_2}
  ~\gbox{\leadsto \lambda \relation{x}{||\rulet_1||}.E} } 
\\ \\

\myrule{Ty-App}
{ \tenv \turns \relation{e_1}{\rulet_1 \arrow \rulet_2}~\gbox{\leadsto E_1} 
  \quad\quad\quad
  \tenv \turns \relation{e_2}{\rulet_1}~\gbox{\leadsto E_2}
}
{ \tenv \turns \relation{e_1\,e_2}{\rulet_2}~\gbox{\leadsto E_1\,E_2}} 
\\ \\

  \myrule  {Ty-TAbs}
           {  \tenv,\alpha \turns \relation{e}{\rulet}~\gbox{\leadsto E_1} 
           }
           { \tenv \turns \relation{\Lambda \alpha.e}{\forall
               \alpha.\rulet}~\gbox{\leadsto \Lambda \alpha.E_1} }
\\ \\
  \myrule  {Ty-TApp}
           { \tenv \turns \relation{e}{\forall \alpha.\rulet_2}~\gbox{\leadsto E}
              \quad\quad\quad
              \tenv \turns \rulet_1 
           }
           { \tenv \turns \relation{e\,\rulet_1}{\rulet_2 [\rulet_1 /\alpha]}~\gbox{\leadsto
    E~||\rulet_1||}} 
\\ \\
  \myrule  {Ty-IAbs}
           { \tenv, \rulet_1 \gbox{\leadsto x} \turns \relation{e}{\rulet_2}~\gbox{\leadsto
    E} 
             \quad \tenv \turns \rulet_1 
             \quad \unamb \rulet_1
             \quad \gbox{x~\mathit{fresh}}}
           { \tenv \turns \relation{\ilambda \rulet_1.e}{\rulet_1 \iarrow \rulet_2}~\gbox{\leadsto
    \lambda \relation{x}{||\rulet_1||}. E}}
\\ \\
  \myrule  {Ty-IApp}
           { \tenv \turns \relation{e_1}{\rulet_2 \iarrow
      \rulet_1~\gbox{\leadsto E_1}} 
             \quad\quad\quad
             \tenv \turns \relation{e_2}{\rulet_2}~\gbox{\leadsto E_2}}
           { \tenv \turns \relation{e_1 \with e_2}{\rulet_1}~\gbox{\leadsto
    E_1~E_2}}
\\ \\
\myrule {Ty-Query}
{ \tenv \vturns \rulet~\gbox{\leadsto E} \quad\quad\quad \tenv \turns \rulet \quad\quad\quad \unamb \rulet}
{ \tenv \turns \relation{?\rulet}{\rulet}~\gbox{\leadsto E}
} 
\eda
\end{minipage}
}
\end{center}
}

Figure \ref{fig:type} presents the static type system of $\name$.
Our language is based on System~F, which is included in our system.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Well-Formed Types}
As in System F, a type environment $\tenv$ records type variables $\alpha$
and variables $x$ with associated types $\rulet$ that are in scope.
New here is that it also records instances of implicits $\rulet$.
\bda{llrl} 
\text{Type Environments}     & \tenv & ::= & \epsilon \mid \tenv, \relation{x}{\rulet} \mid \tenv , \alpha \mid \tenv, \rulet~\gbox{\leadsto x} \\
\eda
Judgement $\tenv \turns \rulet$ holds if type $\rulet$ is well-formed 
with respect to type environment $\tenv$, that is, if all free type variables
of $\rulet$ occur in $\tenv$.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Well-Typed Expressions}

Typing judgment ${\tenv \turns \relation{e}{\rulet}}$ holds if
expression $e$ has type $\rulet$ with respect to type environment $\tenv$.
The first five rules copy the corresponding System F rules; only the last three deserve special attention.
Firstly, rule \TyIAbs{} extends the implicit environment with the type of an implicit instance.
The side condition $\unamb \rulet_1$ states that
the type $\rulet_1$ must be unambiguous; we explain this concept in Section~\ref{subsec:det}.
Secondly, rule \TyIApp{} eliminates an implicit abstraction by supplying an
instance of the required type. Finally, rule \TyQuery{} resolves 
a given type $\rulet$ against the implicit environment.
Again, a side-condition states that $\rulet$ must be unambiguous.
Resolution is defined in terms of the auxiliary judgement $\tenv \vturns \rulet$, which
is explained next. 

%-------------------------------------------------------------------------------
\subsection{Resolution}\label{s:resolution}

\figtwocol{fig:resolution1}{Ambiguous Resolution}{
\begin{center}
\framebox{\scriptsize
\begin{minipage}{.969\textwidth}
\bda{c}
\myruleform{\tenv \vturns \rulet~\gbox{\leadsto E}}
\\ \\
  \myrule {AR-IVar}
          {\rulet~\gbox{\leadsto x} \in \tenv}
          {\tenv \vturns \rulet~\gbox{\leadsto x}}
\\ \\
  \myrule {AR-TAbs}
          {\tenv, \alpha \vturns \rulet~\gbox{\leadsto E}}
          {\tenv \vturns \forall \alpha. \rulet~\gbox{\leadsto \Lambda\alpha.E}} 
\quad
  \myrule {AR-IAbs}
          {\tenv, \rulet_1~\gbox{\leadsto x} \vturns \rulet_2~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
          {\tenv \vturns \rulet_1 \iarrow \rulet_2~\gbox{\leadsto
            \lambda\relation{x}{||\rulet_1||}.E}} 
\\ \\
  \myrule {AR-TApp}
          {\tenv \vturns \forall \alpha. \rulet~\gbox{\leadsto E} \quad\quad \Gamma \turns \rulet'}
          {\tenv \vturns \rulet[\rulet'/\alpha]~\gbox{\leadsto E~||\rulet'||}}
\quad
  \myrule {AR-IApp}
          {\tenv \vturns \rulet_1 \iarrow \rulet_2~\gbox{\leadsto E_2} \quad\quad \tenv \vturns \rulet_1~\gbox{\leadsto E_1}}
          {\tenv \vturns \rulet_2~~\gbox{\leadsto E_2~E_1}}
\eda
\end{minipage}
}
\end{center}
}

Figure~\ref{fig:resolution1} provides a first, ambiguous definition of the
resolution judgement. Its underlying principle is
resolution in logic. 
Intuitively, $\tenv\vturns \rulet$ holds if $\tenv$ entails $\rulet$, where the types in $\tenv$ and
$\rulet$ are read as propositions, where $r$ stands for resolution and $a$ for ambiguous.
Following the ``Propositions as Types'' correspondence~\cite{propsastypes}, we read
$\alpha$ as a propositional variable and $\forall \alpha.\rulet$ as universal quantification.
Yet, unlike in the traditional interpretation of types as propositions, we have two forms of arrows,
functions $\rulet_1 \arrow \rulet_2$ and rules $\rulet_1 \iarrow \rulet_2$,
and the important twist is that we choose to treat
only rules as implications, leaving functions as uninterpreted predicates.

% Figure~\ref{fig:resolution1} provides a first (ambiguous) definition of the
% resolution judgement $\tenv \vturns \rulet$ that corresponds to the intuition of
% logical implication checking. 
% 
Unfortunately, the definition in Figure~\ref{fig:resolution1} suffers from two problems. 
% \begin{enumerate}
% \item 
Firstly, the definition is \emph{not syntax-directed}; several of the inference
rules have overlapping conclusions. Hence, a deterministic resolution algorithm
is non-obvious.
% \item
Secondly and more importantly, the definition is \emph{ambiguous}: a derivation
can be shown by multiple different derivations. For instance, 
consider resolution under the environment
\[
\Gamma_0 = \tyint,\tybool,(\tybool\iarrow\tyint)
\]
there are two different derivations for
$\Gamma_0 \vturns \tyint$:
\begin{equation*}
\begin{array}{c}
\inferrule*[Left=\mylabel{AR-IVar}]
   {\tyint \in \Gamma_0}
   {\Gamma_0 \vturns \tyint}
\end{array}
\end{equation*}
and
\begin{equation*}
\begin{array}{c}
\inferrule*[Left=\mylabel{AR-IApp}]
   {\inferrule*[Left=\mylabel{AR-IVar}] {(\tybool \iarrow \tyint) \in \Gamma_0}
                {\Gamma_0 \vturns (\tybool \iarrow \tyint)} \\
    \inferrule*[left=\mylabel{AR-IVar}] {\tybool \in \Gamma_0}
                {\Gamma_0 \vturns \tybool}
   }
   {\Gamma_0 \vturns \tyint}
\end{array}
\end{equation*}
While this may seem harmless at the type-level, at the value-level each
derivation corresponds to a (possibly) different value. Hence, ambiguous
resolution renders the meaning of a program ambiguous.
% \end{enumerate}

We next address these two issues one by one.

%-------------------------------------------------------------------------------
\subsection{Type-Directed Resolution with Focusing}

To obtain a type-directed formulation of resolution, we adopt a solution from
proof search known as \emph{focusing}~\cite{focusing}. This solution makes sure
that only one inference rule applies at any given point and thereby rules out
gratuitous forms of nondeterminism. 

As an example of such gratuitous nondeterminism consider
the following two ways of resolving $a$ given 
$\tenv = a~\gbox{\leadsto x}$:
\begin{equation*}
\begin{array}{c}
\inferrule*[left=(AR-IVar)]
   {a~\gbox{\leadsto x} \in \tenv}
   {\tenv \vturns a~\gbox{\leadsto x}}
\end{array}
\end{equation*}
% ==========
% TC a |= a

\noindent
versus
\begin{equation*}
\begin{array}{c}
\inferrule*[left=(AR-IApp)]
   {
      \inferrule*[left=(AR-IAbs)]
         {
            \inferrule*[left=(AR-IVar)]
               { a~\gbox{\leadsto y} \in \tenv, a~\gbox{\leadsto y}}
               { \tenv, a~\gbox{\leadsto y} \vturns a ~\gbox{\leadsto y} }
         }
         {\tenv \vturns a \iarrow a ~\gbox{\leadsto \lambda y. y}} \\
      \inferrule*[left=(AR-IVar)]
         {a ~\gbox{\leadsto x} \in \tenv}
         {\tenv \vturns a ~\gbox{\leadsto x}}
   }
   {\tenv \vturns a~\gbox{\leadsto (\lambda y.y)\,x}}
\end{array}
\end{equation*}
While these are two different proofs, they use the information in the context
$\tenv$ in essentially the same way. Hence, unlike the nondeterminism in the
previous example at the end of Section~\ref{s:resolution} where the context provides two
ways of resolving the query, this form of nondeterminism
serves no purpose.
We will see that focusing provides a straightjacket that eliminates the gratuitous nondeterminism
and allows only the first and more direct of these two proofs. 

% More generally, without loss of
% expressivity focusing only allows proofs whose elaboration is in
% $\beta$-reduced and $\eta$-expanded form.
% 
% they do not lead to different behavior -- the elaborated terms in grey
% are $\beta$-equivalent. 

\figtwocol{fig:resolutionf}{Focusing Resolution}{
\begin{center}
\framebox{\scriptsize
\begin{minipage}{.969\textwidth}
\bda{c}
\Sigma ::= \epsilon \mid \Sigma, \rulet~\gbox{\leadsto x} \\ \\
\myruleform{\tenv \fturns [\rulet]~\gbox{\leadsto E}}
\\ \\
  \myrule {FR-TAbs}
          {\tenv, \alpha \fturns [\rulet]~\gbox{\leadsto E}}
          {\tenv \fturns [\forall \alpha. \rulet]~\gbox{\leadsto \Lambda\alpha.E}} 
\quad
  \myrule {FR-IAbs}
          {\tenv, \rulet_1~\gbox{\leadsto x} \fturns [\rulet_2]~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
          {\tenv \fturns [\rulet_1 \iarrow \rulet_2]~\gbox{\leadsto
            \lambda\relation{x}{||\rulet_1||}.E}} 
\\ \\
  \myrule {FR-Simp}
          {\rulet~\gbox{\leadsto x} \in \tenv \\ 
           \tenv; [\rulet]~\gbox{\leadsto x} \fturns \type~\gbox{\leadsto E};\bar{\rulet}' ~\gbox{\leadsto \bar{x}'}  \\
           \tenv \fturns [\rulet']~\gbox{\leadsto E'} \enskip (\forall \rulet' \in \bar{\rulet}')
          }
          {\tenv \fturns [\type]~\gbox{\leadsto E[\bar{E}'/\bar{x}']}}
\\ \\
\myruleform{\tenv; [\rulet]~\gbox{\leadsto E} \fturns \type~\gbox{\leadsto E'}; \Sigma}
\\ \\
  \myrule {FM-TApp}
          {\tenv \vdash \rulet' \\\\
           \tenv; [[\rulet'/\alpha]\rulet]~\gbox{\leadsto E\,||\rulet'||} \fturns \type~\gbox{\leadsto E'}; \Sigma
          }
          {\tenv; [\forall \alpha.\rulet]~\gbox{\leadsto E} \fturns \type~\gbox{\leadsto E'}; \Sigma}
\\ \\
  \myrule {FM-IApp}
          {\gbox{x~\text{fresh}} \\\\
           \tenv; [\rulet_2]~\gbox{\leadsto E\,x} \fturns \type~\gbox{\leadsto E'}; \Sigma}
          {\tenv; [\rulet_1 \iarrow \rulet_2]~\gbox{\leadsto E} \fturns \type~\gbox{\leadsto E'}; \Sigma, \rulet_1~\gbox{\leadsto x}}
\\ \\
  \myrule {FM-Simp}
          {}
          {\tenv; [\type]~\gbox{\leadsto E} \fturns \type~\gbox{\leadsto E}; \epsilon}

\eda
\end{minipage}
}
\end{center}
}

Figure~\ref{fig:resolutionf} presents our definition of resolution with
focusing. The main judgment $\tenv \fturns [\rulet]~\gbox{\leadsto E}$ is
defined with the help of the auxiliary judgement $\tenv;
[\rulet]~\gbox{\leadsto E} \fturns \type~\gbox{\leadsto E'}; \Sigma$. Both definitions are
by induction on the type $\rulet$ enclosed in square brackets.
The focusing approach refines the grammar of types to distinguish a special
class of \emph{simple} types as the base case of the induction:
{\bda{llrl}
    \text{Context Types} & \rulet \hide{\in 2^\meta{RType}} & ::= & 
    \forall \alpha. \rulet \mid \rulet_1 \iarrow \rulet_2 \mid \type \\
    \text{Simple Types}  & \type                            & ::=  & \alpha \mid \rulet_1 \arrow \rulet_2 \\
  \eda }

The main judgement $\tenv \fturns [\rulet]~\gbox{\leadsto E}$ focuses on the
type $\rulet$ that is to be resolved -- we call this type the ``goal''. There
are three rules, for the three possible syntactic forms of $\rulet$.
%
Rules~\mylabel{FR-TAbs} and~\mylabel{FR-IAbs} decompose the goal by
applying implication and quantifier introductions respectively.  Once the goal
is stripped down to a simple type $\type$,
Rule~\mylabel{FR-Simp} selects a rule $\rulet$ from the
environment $\tenv$ to discharge it. The selected rule must \emph{match} the
goal, a notion that is captured by the auxiliary judgment. Matching
gives rise to a sequence $\Sigma$ of new (and hopefully simpler) goals
that are resolved recursively.

The auxiliary judgment
$\tenv ; [\rulet]~\gbox{\leadsto E} \fturns \type~\gbox{\leadsto E'};\Sigma$ focuses on
the rule $\rulet$ and checks whether it matches the simple goal
$\type$. Again, there are three rules for the three possible forms
the rule can take.
%
Rule~\mylabel{FM-TApp} handles universal quantification by
instantiating the quantified variable $\alpha$ in a way that recursively yields a match.
%
Rule~\mylabel{FM-IApp} handles an implication rule $\rulet_1
\iarrow \rulet_2$ by recursively checking whether $\rulet_2$
matches the goal. At the same time it yields a new goal $\rulet_1$ which
needs to be resolved in order for the rule to apply.
%
Finally, Rule~\mylabel{FM-Simp} 
expresses the base case
where the axiom is identical to the goal and there are no new goals.

It is not difficult to see that this type-directed formulation of entailment
greatly reduces the number of proofs for given goal.
%\footnote{Without loss of expressive power. See for example~\cite{FrankFocusing}.} 
For instance, for the
example above there is only one proof:
\begin{equation*}
\begin{array}{c}
   \inferrule*[left=\mylabel{FR-Simp}]
     { a \in \tenv \\
       \inferrule*[left=\mylabel{FM-Simp}]
         {}
         {\tenv; [a] ~\gbox{\leadsto x} \fturns a~\gbox{\leadsto x}; \epsilon }
     }
     {\tenv \fturns [a] ~\gbox{\leadsto x}}
\end{array}
\end{equation*}

%-------------------------------------------------------------------------------
\subsection{Deterministic and Stable Resolution}\label{subsec:det}

While focusing provides a syntax-directed definition of resolution, it does not
make resolution entirely deterministic. There are still three sources of
non-determinism: 
1) the \emph{impredicative} instantiation of type variable $\alpha$
with a rule type $\rulet'$ in Rule~\mylabel{FM-TApp}, 
2) the \emph{ambiguous} instantiation of type variable $\alpha$
with a rule type $\rulet'$ in Rule~\mylabel{FM-TApp},
and 3) nondeterministic selection of a rule type $\rulet$ from the type environment
$\tenv$ in Rule~\mylabel{FR-Simp}. This section eradicates those three remaining
sources of nondeterminism to obtain an entirely deterministic formulation
of resolution. On top of that, it imposes an additional \emph{stability} condition
to make resolution ``super''-deterministic: resolution is preserved under
type substitution.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Predicative Instantiation}
To see why the impredicative instantation, i.e., the instantiation with types
that contain universal quantifiers, in
Rule~\mylabel{FM-TApp} causes
nondeterminism, consider two ways resolving $\tenv_1 \vdash \tyint \iarrow \tyint$
against the environment $\tenv_1 = \forall \alpha.\alpha \iarrow \alpha$:\footnote{
For the sake of compactness the example uses the original ambiguous definition of resolution.
 Similarly problematic examples can be created for the focusing-based definition.}
\begin{equation*}
\inferrule*[Left=\mylabel{AR-TApp}]
  {\inferrule*[Left=\mylabel{AR-IVar}] 
    {(\forall \alpha.\alpha \iarrow \alpha) \in \tenv_1}
    {\tenv_1 \vturns \forall \alpha. \alpha \iarrow \alpha    }
  }
  {\tenv_1 \vturns \tyint \iarrow \tyint}
\end{equation*}
and
\begin{equation*}
\inferrule*[left=\mylabel{AR-TApp}]
  {\inferrule*[Left=\mylabel{AR-IApp}] 
    { \inferrule*[Left=\mylabel{AR-TApp}]
        { \inferrule*[Left=\mylabel{AR-IVar}]
            {(\forall \alpha. \alpha \iarrow \alpha) \in \tenv_1}
            {\tenv_1 \vturns (\forall \alpha. \alpha \iarrow \alpha)}
        }
        {\tenv_1 \vturns (\forall \beta. \beta \iarrow \beta) \iarrow (\forall \beta. \beta \iarrow \beta)}
        \quad\quad\quad
    \\
      \inferrule*[Left=\mylabel{AR-IVar}]
        {(\forall \beta. \beta \iarrow \beta) \in \tenv_1}
        {\tenv_1 \vturns (\forall \beta. \beta \iarrow \beta)}
    }
    {\tenv_1 \vturns \forall \beta. \beta \iarrow \beta}
  }
  {\tenv_1 \vturns \tyint \iarrow \tyint}
\end{equation*}
The first proof only involves the instantiation of 
$\alpha$ with $\tyint$. Yet, the second proof contains an impredicative
instantiation of $\alpha$ with $\forall \beta. \beta \iarrow \beta$.
Impredicativity is a well-known source of such problems in other settings, such
as in type inference for the polymorphic $\lambda$-calculus~\cite{boehm85,pfenning93}. The established solution also works here: restrict to predicativity. 
For this reason we introduce the syntactic sort of monotypes:
{\bda{llrl}
    \text{Monotypes}     & \suty                            & ::=  & \alpha \mid \suty \arrow \suty
  \eda }
We only allow instantiation with monotypes $\suty$:
\bda{c}
  \myrule {AR-TApp'}
          {\tenv \vturns \forall \alpha. \rulet~\gbox{\leadsto E} \quad\quad \Gamma \turns \rulet'}
          {\tenv \vturns \rulet[\suty/\alpha]~\gbox{\leadsto E~||\suty||}}
\eda
In the focusing-based formulation, this constraint is also enforced:
we only allow instantiation with monotypes $\suty$:
\bda{c}
  \myrule {FM-TApp'}
          {\tenv \vdash \rulet' \\\\
           \tenv; [[\suty/\alpha]\rulet]~\gbox{\leadsto E\,||\suty||} \fturns \type~\gbox{\leadsto E'}; \Sigma
          }
          {\tenv; [\forall \alpha.\rulet]~\gbox{\leadsto E} \fturns \type~\gbox{\leadsto E'}; \Sigma}
\eda

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Non-Ambiguity Constraints}

Rule \mylabel{FM-TApp'} does not explain how the substitution
$[\suty/\alpha]$ for the rule type $\forall \alpha.\rulet$ should be obtained.
At first sight it seems that the choice of $\suty$ is free and thus a source of
non-determinism. However, in many cases the choice is not free at all, but is
instead determined fully by the simple type $\type$ that we want to match.
However, the choice is not always forced by the matching. Take for instance the context type $\forall \alpha. (\alpha \arrow \tystr)
\iarrow (\tystr \arrow \alpha) \iarrow (\tystr \arrow \tystr)$. This 
type encodes the Haskell type |forall a. (Show a, Read a) => String -> String| of the ambiguous expression |read . show|
discussed in Section~\ref{sec:overview-coherence}. 
The
choice of $\alpha$ is ambiguous when matching against the simple type $\tystr
\arrow \tystr$. Yet, the choice is critical for two reasons. Firstly, if we
guess the wrong instantiation $\suty$ for $\alpha$, then it may not be possible
to recursively resolve $(\tystr \arrow \alpha)[\suty/\alpha]$ or $(\alpha \arrow
\tystr)[\suty/\alpha]$, while with a lucky guess both can be resolved.
Secondly, for different choices of $\suty$ the types $(\tystr \arrow
\alpha)[\suty/\alpha]$ and $(\alpha \arrow \tystr)[\suty/\alpha]$ can be resolved
in completely different ways.

In order to avoid any problems, we conservatively forbid all ambiguous context
types in the implicit environment with the $\unamb \rulet_1$
side-condition in rule \mylabel{Ty-IAbs} of Figure~\ref{fig:type}. (An
alternative design to avoid such ambiguity would instantiate unused type
variables to a dummy type, like GHC's \texttt{GHC.Prim.Any}, which is only used
for this purpose.) This judgement is defined in Figure~\ref{fig:unamb}
in terms of the auxiliary judgement $\bar{\alpha} \unamb \rulet$ which
takes an additional sequence of type variables $\alpha$ that is initially
empty.
\figtwocol{fig:unamb}{Unambiguous Context Types}{
\begin{center}
\framebox{
\begin{minipage}{0.969\textwidth}
\bda{c}
\myruleform{\unamb \rulet} 
\quad\quad\quad
\myrule{UA-Main}
       {\epsilon \unamb \rulet}
       {\unamb \rulet}
\\ \\
\myruleform{\bar{\alpha} \unamb \rulet} 
\quad\quad\quad
\myrule{UA-Simp}
       {\bar{\alpha} \subseteq \mathit{ftv}(\type)}
       {\bar{\alpha} \unamb \type}
\\ \\
\myrule{UA-TAbs}
       {\bar{\alpha},\alpha \unamb \rulet}
       {\bar{\alpha} \unamb \forall \alpha.\rulet} 
\quad\quad\quad
\myrule{UA-IAbs}
       {\unamb \rulet_1 \quad\quad \bar{\alpha} \unamb \rulet_2}
       {\bar{\alpha} \unamb \rulet_1 \iarrow \rulet_2} \\ \\
% \mylabel{UA-TAbsAlt} \quad
% \myirule{\bar{\alpha} \vdash_{\mathit{unamb}} \rulet}
%         {\bar{\alpha} \vdash_{\mathit{unamb}} \forall \alpha.\rulet}
% \quad\quad\quad
% \mylabel{UA-IAbsAlt} \quad
% \myirule{\epsilon \vdash_{\mathit{unamb}} \rulet_1 \quad\quad \bar{\alpha},\mathit{ftv}(\rulet_1) \vdash_{\mathit{unamb}} \rulet_2}
%         {\bar{\alpha} \vdash_{\mathit{unamb}} \rulet_1 \iarrow \rulet_2} \\ \\
\eda
\end{minipage}
}
\end{center}
}

The auxiliary judgement expresses that all type variables $\bar{\alpha}$ 
are resolved when matching against $\rulet$.
Its base case, rule \mylabel{UA-Simp}, expresses
that fixing the simple type $\type$ also fixes the type variables
$\bar{\alpha}$. Inductive rule \mylabel{UA-TAbs}
accumulates the bound type variables $\bar{\alpha}$ before the
head. Rule \mylabel{UA-IAbs} skips over any contexts
on the way to the head, but also recursively requires that these contexts are
unambiguous. 

Finally, the unambiguity condition is imposed on the queried type $\rulet$
in rule \mylabel{Ty-Query} because this type too may extend the implicit
environment in rule \mylabel{FR-IAbs}.

Note that the definition rules out harmless ambiguity, such as that in the type
$\forall \alpha. \tyint$. When we match the head of this type $\tyint$ with the
simple type $\tyint$, the matching succeeds without actually determining how
the type variable $\alpha$ should be instantiated. Here the ambiguity is
harmless, because it does not affect the semantics. Yet, for the sake of
simplicity of the metatheory, we have opted to not differentiate between harmless and harmful
ambiguity.


%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Committed Choice}
The other remaining source of nondeterminism is the nondeterministic choice
$\rulet \in \tenv$ that appears in Rule~\mylabel{FR-Simp}. Consider the trivial
example of resolving the goal $\tyint$ against the environment $\tenv = \tyint~\gbox{\leadsto
x}, \tyint~\gbox{\leadsto y}$. Both rules in the environment match the goal and yield
different, i.e., incoherent, elaborations.

Our solution is to replace the nondeterministic relation $\rulet \in \tenv$ by
a deterministic one that selects the first matching rule in the environment and
commits to it. In fact, we replace all three hypotheses of Rule~\mylabel{FR-Simp}
by a new judgement $\tenv;[\tenv'] \ivturns \type~\gbox{\leadsto E}$ which resolves
$\type$ with the first matching rule in the environment $\tenv'$ and performs
any recursive resolutions against the environment $\tenv$. Of course, the modified
Rule~\mylabel{FR-Simp} invokes this judgement with two copies of the same environment, i.e.,
$\tenv' = \tenv$.
\bda{c}
  \myrule {FR-Simp'}
          {\tenv; [\tenv] \ivturns \type~\gbox{\leadsto E}
          }
          {\tenv \fturns [\type]~\gbox{\leadsto E}}
\eda
The (still preliminary) definition of the judgement itself proceeds by structural induction on the
environment $\tenv'$:
\bda{c}
\myruleform{\tenv;[\tenv'] \ivturns \type~\gbox{\leadsto E}}\\ \\

  \myrule{DL-RuleMatch}
          {\tenv; [\rulet]~\gbox{\leadsto x} \ivturns \tau~\gbox{\leadsto E}; \overline{\rulet'~\gbox{\leadsto x}} \\
            \tenv \ivturns [\rulet']~\gbox{\leadsto E'} \quad (\forall \rulet' \in \overline{\rulet}')
          }
          {\tenv;[\tenv',\rulet~\gbox{\leadsto x}] \ivturns \type~\gbox{\leadsto E[\bar{E}'/\bar{x}]}} \\ \\
  \myrule{DL-RuleNoMatch}{
           \not\exists E, \Sigma: \tenv; [\rulet]~\gbox{\leadsto x} \ivturns \type~\gbox{\leadsto E}; \Sigma \\
           \tenv;[\tenv'] \ivturns \type~\gbox{\leadsto E'}
          }
          {\tenv;[\tenv',\rulet~\gbox{\leadsto x}] \ivturns \type~\gbox{\leadsto E'}} \\ \\
  \myrule{DL-Var}
         {\tenv;[\tenv'] \ivturns \type~\gbox{\leadsto E}
         }
         {\tenv;[\tenv',x:\rulet] \ivturns \type~\gbox{\leadsto E}} 
\quad\quad\quad
  \myrule{DL-TyVar}
         {\tenv;[\tenv'] \ivturns \type~\gbox{\leadsto E}
         }
         {\tenv;[\tenv',\alpha] \ivturns \type~\gbox{\leadsto E}} 
\eda

Rule~\mylabel{DL-RuleMatch} concerns the case where the first entry in the 
environment matches the goal. Its behavior is the same as in the
original definition of Rule~\mylabel{FR-Simp}.

Rule~\mylabel{DL-RuleNoMatch} is mutually exclusive with the above rule: it
skips the first entry in the environment only iff it does not match to look for
a matching rule deeper in the environment. This implements the committed choice
semantics: the first matching rule is committed to and further rules are not
considered.

Finally, Rules~\mylabel{DL-Var} and \mylabel{DL-TyVar} skip the irrelevant
non-rule entries in the type environment.

It is not difficult to see that with the above definition there is only one way
to resolve the goal $\tyint$ against the environment $\tenv =
\tyint~\gbox{\leadsto x}, \tyint~\gbox{\leadsto y}$. The first matching
entry, which elaborates to $y$, is committed to and the second entry is not
considered.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Stability}

While the above committed-choice formulation of resolution is deterministic, it
is a rather fragile, or \emph{unstable}, notion of resolution. Consider for
example resolving the goal $\tyint$ against the environment $\tenv =
\tyint~\gbox{\leadsto x}, \alpha~\gbox{\leadsto y}$.  This scenario
arises for instance when type checking the expression $e = \ilambda \tyint. (\Lambda \alpha. \ilambda \alpha. \query \tyint)\,\tyint$.
Our definition of resolution skips the first entry in the environment because $\alpha$ does not
match $\tyint$, commits to the second entry because $\tyint$ obviously matches
$\tyint$, and elaborates to $x$.

However, this resolution is not stable. Consider what happens when we apply a
seemingly innocuous refactoring to the expression $e$ by $\beta$-reducing the
type application. This yields the new, and supposedly equivalent, expression
$e' = \ilambda \tyint. \ilambda \tyint. \query \tyint$.  The direct impact of
this refactoring on the resolution problem is to substitute $\tyint$ for the type variable
$\alpha$. As a consequence the resolution commits now to the first
entry and elaborates to $y$ instead of $x$. Hence, more generally, the above
definition of resolution is not stable under type substitution. This is problematic
because it defies the common expectation that simple refactorings like the one
above do not change a program's behavior.

To avoid this problem and obtain stability under type substitution, we tighten
the requirement of Rule~\mylabel{DL-RuleNoMatch}: a
rule in the environment can only be skipped iff that rule does not match under any possible
substitution of type variables. With this tightened requirement the scenario
above simply does not resolve: unstable resolutions are invalid.
\bda{c}
  \myrule{DL-RuleNoMatch'}{
	\mathit{stable}(\tenv,\rulet~\gbox{\leadsto x},\type) \\
%   \not\exists \theta, E, \Sigma, \mathit{dom}(\theta) \subseteq \bar{\alpha}: \theta(\tenv); \theta(\rulet)~\gbox{\leadsto x} \ivturns \theta(\tau)~\gbox{\leadsto E}; \Sigma \\
           \tenv;[\tenv'] \ivturns \type~\gbox{\leadsto E'}
          }
          {\tenv;[\tenv',\rulet~\gbox{\leadsto x}] \ivturns \type~\gbox{\leadsto E'}}
\eda
where a first stab at a formalisation of the stability condition is:
\bda{c}
\myruleform{\mathit{stable}(\tenv,\rulet~\gbox{\leadsto x},\type)} \\ \\
  \myrule{Stable}{\not\exists \theta, \gbox{E}, \Sigma:\enskip \theta(\tenv); [\theta(\rulet)]~\gbox{\leadsto x} \ivturns \theta(\tau)~\gbox{\leadsto E}; \Sigma}
          {\mathit{stable}(\tenv,\rulet~\gbox{\leadsto x},\type)}
\eda

The above formulation of the condition is a bit too lax; we have to be more
precise about the domain and range of the substitution $\theta$.  Indeed,
substitution does not make sense for every type variable in the environment.
Consider for example resolving the type $\forall \beta. \beta \arrow \beta$
against the environment $\tenv_0 = \forall \gamma. \gamma \arrow
\gamma~\gbox{\leadsto x}, \alpha, \alpha \arrow \alpha ~\gbox{\leadsto y}$.
Clearly, we would like to this resolution of $\forall \beta. \beta \to \beta$
to succeed against $\forall \gamma. \gamma \to \gamma$.

Unfortunately, the above formulation of stability unnecessarily throws a
spanner in the works. Consider what happens:
Using
Rule~\mylabel{FR-TAbs}, we would recursively resolve $\beta \arrow \beta$
against the extended environment $\tenv_1 = \tenv_0, \beta$. Next we get stuck
as neither Rule~\mylabel{DL-RuleMatch} nor Rule~\mylabel{DL-RuleNoMatch'}
applies. The former does not apply because $\alpha \arrow \alpha$ does not
match $\beta \arrow \beta$.  Also the latter does not apply because there are
two substitutions such that $\theta(\alpha \arrow \alpha)$ matches
$\theta(\beta \arrow \beta)$ and hence skipping $\alpha \arrow \alpha$ is
deemed unstable.

However, if we look more closely at these substitutions, we see that none of
them make sense. Essentially, there are two groups of substitutions:
\begin{itemize}
\item Those substitutions that instantiate $\beta$, of which $\theta =
      [\alpha/\beta]$ is a prominent example. These substitutions do not make sense
      because code inlining cannot result in $\beta$ being instantiated to
      $\alpha$ or to any other type, because $\beta$ is not in scope
      at the point in the code where the query happens (i.e., $\beta$ does not appear in $\tenv_0$).
      Hence, considering substitutions of $\beta$ does not make sense.

      Figure~\ref{fig:resolution2}, which puts all the measures together to
      obtain a type-directed, deterministic and stable resolution, addresses the
      issue as follows. It introduces a top-level judgement $\tenv \ivturns \rulet ~\gbox{\leadsto E}$
      to handle a query that delegates to the focusing-based judgements we have described above.
      The only contribution of the new main judgement, which is defined by a single rule, is to gather the type variables $\bar{\alpha}$
      that appear in the environment at the point of the query by means of the function $\tyvars{\tenv}$, 
      and to pass them on through the auxiliary judgements to the point where the stability check is performed.
      Hence, the auxiliary judgements $\bar{\alpha}; \tenv \ivturns \rulet~\gbox{\leadsto E}$, $\bar{\alpha}; \tenv; \tenv' \ivturns \type~\gbox{\leadsto E}$
      and $\mathit{stable}(\bar{\alpha};\tenv;\rulet~\gbox{\leadsto x};\type)$ now all feature an additional argument $\bar{\alpha}$ of
      type variables that can be substituted.

\item The substitution $\theta' = [\beta/\alpha]$ also generates a match. However, this 
      substitution does not make sense either because code inlining can only result in substitutions 
      of $\alpha$ by types that are well-scoped in the prefix of the environment before $\alpha$.
      In the case of the example this means that we can only considering substitutions
      $[\rulet/\alpha]$ where $\forall \gamma. \gamma \arrow \gamma~\gbox{\leadsto x} \vdash \rulet$. In
      other words, $\rulet$ cannot have any free type variables. Obviously there is no such
      $\rulet$ that yields a match.
\end{itemize}
 
In summary, Figure~\ref{fig:subst} formalises our notion of valid substitutions
with the judgement $\bar{\alpha};\tenv \vdash \theta$. It assumes an inductive
syntax for substitutions as sequences of single variable substitutions.
{\bda{llrl}
    \text{Substitutions}     & \theta & ::=  & \epsilon \mid [\rulet/\alpha] \cdot \theta
  \eda }
Rule~\mylabel{S-Empty} states that the empty substitution is $\epsilon$ is
trivially valid. Rule~\mylabel{S-Cons} covers the inductive case
$[\rulet/\alpha] \cdot \theta$. It says that the single variable substitution
$[\rulet/\alpha]$ is valid if $\alpha$ appears in the sequence of substitutable type
variables, expressed by the structural pattern $\bar{\alpha},\alpha,\bar{\alpha}'$.
Moreover, $\alpha$ must appear in the type environment, expressed by a similar
structural pattern $\tenv,\alpha,\tenv'$. Lastly, the type $\rulet$ must be well-scoped
with respect to the environment prefix $\tenv$.
In addition, the remainder $\theta$ must be valid with respect to the remaining type
variables $\bar{\alpha},\bar{\alpha}'$ and the type environment after substitution of $\alpha$.


  
\figtwocol{fig:subst}{Valid Substitutions}{ \begin{center}
\framebox{\scriptsize \begin{minipage}{0.969\textwidth} \bda{c} \theta ::=
\epsilon \mid [\rulet/\alpha] \cdot \theta \\ \\
\myruleform{\bar{\alpha};\tenv\vdash\theta} \\ \\ \myrule {S-Empty} {}
{\bar{\alpha}; \tenv \vdash \epsilon} \\ \\ \myrule {S-Cons} {\tenv \vdash
\rulet \\ \bar{\alpha},\bar{\alpha'}; \tenv, \theta(\tenv') \vdash \theta }
{\bar{\alpha},\alpha,\bar{\alpha'}; \tenv, \alpha, \tenv' \vdash
[\rulet/\alpha] \cdot \theta} \eda \end{minipage} } \end{center} }
   
%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Summary}

\figtwocol{fig:resolution2}{Deterministic Resolution and Translation to System F}{
\begin{center}
\framebox{\scriptsize
\begin{minipage}{0.969\textwidth}
\bda{c}
\Sigma ::= \epsilon \mid \Sigma, \rulet~\gbox{\leadsto x} \\ \\
\myruleform{\tenv \ivturns \rulet~\gbox{\leadsto E}} \\ \\
  \myrule {R-Main}
          {\tyvars{\tenv};\tenv \ivturns [\rulet]~\gbox{\leadsto E}}
          {\tenv \ivturns \rulet~\gbox{\leadsto E}} \\ \\
\left.
\begin{array}{rcl@@{\hspace{1.5cm}}rcl}
\tyvars{\epsilon}     & = & \epsilon &
\tyvars{\tenv,\alpha} & = & \tyvars{\tenv},\alpha \\
\tyvars{\tenv,x : \rulet} & = & \tyvars{\tenv} &
\tyvars{\tenv,\rulet~\gbox{\leadsto x}} & = & \tyvars{\tenv} 
\end{array}
\right. \\ \\
\multicolumn{1}{c}{\myruleform{\bar{\alpha}; \tenv \ivturns [\rulet]~\gbox{\leadsto E}}} \\ \\
%%\quad\quad\quad
  \myrule{R-IAbs}
         {\bar{\alpha};\tenv, \rulet_1~\gbox{\leadsto x} \ivturns [\rulet_2]~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
         {\bar{\alpha};\tenv \ivturns [\rulet_1 \iarrow \rulet_2]~\gbox{\leadsto
            \lambda\relation{x}{||\rulet_1||}.E}} 
\quad\quad
  \myrule{R-TAbs}
         {\bar{\alpha};\tenv,\alpha \ivturns [\rulet]~\gbox{\leadsto E}}
         {\bar{\alpha};\tenv \ivturns [\forall \alpha. \rulet]~\gbox{\leadsto \Lambda\alpha.E}} 
\\ \\
 \myrule{R-Simp}
        {\bar{\alpha};\tenv;[\tenv] \ivturns \type~\gbox{\leadsto E}}
        {\bar{\alpha};\tenv \ivturns [\type]~\gbox{\leadsto E}} 
\\ \\ \\
\myruleform{\bar{\alpha};\tenv;[\tenv'] \ivturns \type~\gbox{\leadsto E}}\\ \\

  \myrule{L-RuleMatch}
          {\tenv; [\rulet]~\gbox{\leadsto x} \ivturns \tau~\gbox{\leadsto E}; \overline{\rulet'~\gbox{\leadsto x}} \\
            \bar{\alpha};\tenv \ivturns [\rulet']~\gbox{\leadsto E'} \quad (\forall \rulet' \in \overline{\rulet}')
          }
          {\bar{\alpha};\tenv;[\tenv',\rulet~\gbox{\leadsto x}] \ivturns \type~\gbox{\leadsto E[\bar{E}'/\bar{x}]}} \\
  \myrule{L-RuleNoMatch}{
	\mathit{stable}(\bar{\alpha},\tenv,\rulet~\gbox{\leadsto x},\type) \\
%   \not\exists \theta, E, \Sigma, \mathit{dom}(\theta) \subseteq \bar{\alpha}: \theta(\tenv); \theta(\rulet)~\gbox{\leadsto x} \ivturns \theta(\tau)~\gbox{\leadsto E}; \Sigma \\
           \bar{\alpha};\tenv;[\tenv'] \ivturns \type~\gbox{\leadsto E'}
          }
          {\bar{\alpha};\tenv;[\tenv',\rulet~\gbox{\leadsto x}] \ivturns \type~\gbox{\leadsto E'}} \\ \\
  \myrule{L-Var}
         {\bar{\alpha};\tenv;[\tenv'] \ivturns \type~\gbox{\leadsto E}
         }
         {\bar{\alpha};\tenv;[\tenv',x:\rulet] \ivturns \type~\gbox{\leadsto E}} 
\quad\quad\quad
  \myrule{L-TyVar}
         {\bar{\alpha};\tenv;[\tenv'] \ivturns \type~\gbox{\leadsto E}
         }
         {\bar{\alpha};\tenv;[\tenv',\alpha] \ivturns \type~\gbox{\leadsto E}} 
\\ \\ \\
\myruleform{\tenv; [\rulet]~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma}\\ \\
  \myrule{M-Simp}
         {}
         {\tenv; [\type]~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E}; \epsilon} \\ \\
  \myrule{M-IApp}
         {\tenv, \rulet_1 \gbox{\leadsto x}; [\rulet_2] ~\gbox{\leadsto E\,x} \ivturns \type~\gbox{\leadsto E'}; \Sigma 
          \quad\quad\quad \gbox{x~\mathit{fresh}}
         }
         {\tenv; [\rulet_1 \iarrow \rulet_2] ~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma, \rulet_1~\gbox{\leadsto x}} \\ \\ 
  \myrule{M-TApp}
         {\tenv; [\rulet[\suty/\alpha]] ~\gbox{\leadsto E\,||\suty||} \ivturns \type~\gbox{\leadsto E'}; \Sigma
          \quad\quad\quad
          \tenv \turns \suty
         }
         {\tenv; [\forall \alpha. \rulet] ~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma} \\ \\ \\
\myruleform{\mathit{stable}(\bar{\alpha},\tenv,\rulet~\gbox{\leadsto x},\type)} \\ \\
  \myrule{Stable}{\not\exists \theta, E, \Sigma: \enskip \bar{\alpha},\tenv \vdash \theta
           \quad \theta(\tenv); [\theta(\rulet)]~\gbox{\leadsto x} \ivturns \theta(\tau)~\gbox{\leadsto E}; \Sigma}
          {\mathit{stable}(\bar{\alpha},\tenv,\rulet~\gbox{\leadsto x},\type)}
\eda
\end{minipage}
}
\end{center}
} 

Figure~\ref{fig:resolution2} puts all the above measures together in our
unambiguous, deterministic and stable definition of resolution.

% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
% \paragraph{Legacy}
% 
% % forall a. a => a |- int => int
% 
% % In order to eradicate the non-determinism in resolution we implement the following
% % measures:
% % \begin{enumerate}
% % \item We provide a syntax-directed definition of resolution, based on the idea of
% %       \emph{focused proof search} in logic~\cite{focusing,Miller91b,Liang:2009}, where at most one
% %       rule applies in any given situation. 
% % 
% %       Our approach organizes resolution into two alternating phases that
% %       pivots on an environment lookup (\mylabel{R-IVar}) which shifts
% %       the focus from the queried type to an implicit rule type in the environment. 
% %       The first phase performs \emph{backward chaining}: it applies only
% %       elimination rules (\mylabel{R-TAbs},\mylabel{R-IAbs}) to the query type
% %       to reason towards the given rules in the environment.
% % 
% %       In constrast, the second phase performs \emph{forward chaining}; it
% %       reasons from the selected environment rule towards the query type. It does so
% %       by applying only introduction rules (\mylabel{R-TApp},\mylabel{R-IApp}), but in
% %       \emph{inverted form}, i.e., from the environment type towards the query type.
% % 
% % \item Our approach differs from focused proof search in the selection of the focus.
% %       This is typically a nondeterminstic choice in focused proof search, but we make
% %       it deterministic in two ways: 
% %       \begin{enumerate}
% %       \item by implementing a stack discipline: only the first (in LIFO order) matching rule type can be selected, and
% %       \item we do not include any recursive resolutions in the matching decisions; this keeps
% %             matching a shallow procedure which does not require any form of backtracking.
% %       \end{enumerate}
% % 
% % \item We rule out two forms of non-determinism in the instantiation of
% %       polymorphic types:
% %       \begin{enumerate}
% %       \item We disallow ambiguous types where quantified type variables
% %             are not determined by the head of the type, such as 
% %             $\forall \alpha.\tyint$ or $\forall \alpha. \alpha \iarrow \tyint$.
% % 
% %       \item We do not allow type variables to be instantiated by types with
% %             abstractions (universal quantifiers or implicit arrows) as these
% %             may subsequently be eliminated again (possibly by instantiation 
% %             with other abstractions). For instance, $\forall \alpha. \alpha \iarrow \alpha$
% % 	    can be instantiated directly with $[\tyint/\alpha]$ to $\tyint
% % \iarrow \tyint$.  Alternatively, it could be first instantiated with $[(\forall
% % \beta. \beta \iarrow \beta)/\alpha]$ to $(\forall \beta. \beta \iarrow \beta)
% % \iarrow \forall \beta'. \beta' \iarrow \beta'$, and then after further
% % instantiation of the outer context and of $\beta'$ with $[\tyint/\beta']$ also
% % to $\tyint \iarrow \tyint$.
% %  
% %       \end{enumerate}
% % 
% % \end{enumerate}
% 
% Figure~\ref{fig:resolution2} defines judgement $\tenv \ivturns \rulet$, which
% is a syntax-directed deterministic variant of $\tenv \vturns \rulet$. This
% deterministic variant is sound with respect to the ambiguous definition. In
% other words, $\tenv \vturns \rulet$ holds if $\tenv \ivturns \rulet$ holds.
% Yet, the opposite is not true. The deterministic judgement sacrifices some
% expressive power in exchange for better behavedness.
% 
% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
% \paragraph{Revised Syntax}
% 
% To facilitate the definition of the deterministic resolution
% judgement we split the syntax of types into three different
% sorts: \emph{context} types, \emph{simple} types and \emph{monotypes}.
% {\bda{llrl}
%     \text{Context Types} & \rulet \hide{\in 2^\meta{RType}} & ::= & 
%     \forall \alpha. \rulet \mid \rulet_1 \iarrow \rulet_2 \mid \type \\
%     \text{Simple Types}  & \type                            & ::=  & \alpha \mid \rulet_1 \arrow \rulet_2 \\
%     \text{Monotypes}     & \suty                            & ::=  & \alpha \mid \suty \arrow \suty
%     % \text{Expressions} & |e| & ::=  &
%     % x \mid \lambda (x:\rulet).e \mid e_1\,e_2 \mid \Lambda \alpha. e \mid e\,\rulet \mid \query \rulet \mid \ilambda \rulet. e \mid e_1 \with e_2 \\
%   \eda }
% 
%  \emph{Context types} $\rulet$ correspond to the original types $\rulet$.
% \emph{Simple types} $\type$ are a restricted form of context types without
% toplevel quantifiers and toplevel implicit arrows. Singling out this restricted
% form turns out to be convenient for the type-directed formulation of the judgement.
% 
% \emph{Monotypes} $\suty$ are a further refinement of simple types without
% universal quantifiers and implicit arrows anywhere. They help us to address a
% form of ambiguity due to the \emph{impredicativity} of Rule~\mylabel{AR-TApp}.
% For instance, if we define $\tenv_1 = \forall \alpha.\alpha \iarrow \alpha$,
% then there are two ways to resolve $\tenv_1 \vdash \tyint \iarrow \tyint$: 
% 
% %       \item We do not allow type variables to be instantiated by types with
% %             abstractions (universal quantifiers or implicit arrows) as these
% %             may subsequently be eliminated again (possibly by instantiation 
% %             with other abstractions). For instance, $\forall \alpha. \alpha \iarrow \alpha$
% % 	    can be instantiated directly with $[\tyint/\alpha]$ to $\tyint
% % \iarrow \tyint$.  Alternatively, it could be first instantiated with $[(\forall
% % \beta. \beta \iarrow \beta)/\alpha]$ to $(\forall \beta. \beta \iarrow \beta)
% % \iarrow \forall \beta'. \beta' \iarrow \beta'$, and then after further
% % instantiation of the outer context and of $\beta'$ with $[\tyint/\beta']$ also
% % to $\tyint \iarrow \tyint$.
% \begin{equation*}
% \inferrule*[Left=\mylabel{AR-TApp}]
%   {\inferrule*[Left=\mylabel{AR-IVar}] 
%     {(\forall \alpha.\alpha \iarrow \alpha) \in \tenv_1}
%     {\tenv_1 \vturns \forall \alpha. \alpha \iarrow \alpha    }
%   }
%   {\tenv_1 \vturns \tyint \iarrow \tyint}
% \end{equation*}
% and
% \begin{equation*}
% \inferrule*[left=\mylabel{AR-TApp}]
%   {\inferrule*[Left=\mylabel{AR-IApp}] 
%     { \inferrule*[Left=\mylabel{AR-TApp}]
%         { \inferrule*[Left=\mylabel{AR-IVar}]
%             {(\forall \alpha. \alpha \iarrow \alpha) \in \tenv_1}
%             {\tenv_1 \vturns (\forall \alpha. \alpha \iarrow \alpha)}
%         }
%         {\tenv_1 \vturns (\forall \beta. \beta \iarrow \beta) \iarrow (\forall \beta. \beta \iarrow \beta)}
%         \quad\quad\quad
%     \\
%       \inferrule*[Left=\mylabel{AR-IVar}]
%         {(\forall \beta. \beta \iarrow \beta) \in \tenv_1}
%         {\tenv_1 \vturns (\forall \beta. \beta \iarrow \beta)}
%     }
%     {\tenv_1 \vturns \forall \beta. \beta \iarrow \beta}
%   }
%   {\tenv_1 \vturns \tyint \iarrow \tyint}
% \end{equation*}
% 
% The first proof only involves the predicative generalisation from
% $\tyint$ to $\alpha$. Yet, the second proof contains an impredicative
% generalisation from $\forall \beta. \beta \iarrow \beta$ to $\alpha$.
% Impredicativity is a well-known source of such problems in other settings, such
% as in type inference for the polymorphic $\lambda$-calculus~\cite{boehm85,pfenning93}. The established solution also works here: restrict to predicativity. This is where the monotype
% sort $\suty$ comes in: we only allow generalisation over (or dually,
% instantiation with) monotypes $\suty$.
% 
% % ------------------------------------ R-IVar
% % forall a. a => a |- forall a. a => a
% % ------------------------------------ R-TApp
% % forall a. a => a |- int => int
% % 
% % 
% % ------------------------------------ R-IVar
% % forall a. a => a |- forall a. a => a
% % ------------------------------------------------------------ R-TApp
% % forall a. a => a |- (forall b. b => b) => (forall b. b => b)              ...
% % ------------------------------------------------------------------------------------------
% % forall a. a => a |- forall b. b => b
% % ------------------------------------ R-TApp
% % forall a. a => a |- int => int
% 
% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
% \paragraph{Revised Resolution Rules}
% 
% \newcommand{\elookup}[3][\bar{\alpha}]{{#2}_{#1}\langle{#3}\rangle}
% 
% \figtwocol{fig:resolution2}{Deterministic Resolution and Translation to System F}{
% \begin{center}
% \framebox{\scriptsize
% \begin{minipage}{0.969\textwidth}
% \bda{c}
% \Sigma ::= \epsilon \mid \Sigma, \rulet~\gbox{\leadsto x} \\ \\
% \myruleform{\tenv \ivturns \rulet~\gbox{\leadsto E}} \\ \\
%   \myrule {R-Main}
%           {\mathit{tyvars}(\tenv);\tenv \ivturns \rulet~\gbox{\leadsto E}}
%           {\tenv \ivturns \rulet~\gbox{\leadsto E}} \\ \\
% \multicolumn{1}{c}{\myruleform{\bar{\alpha}; \tenv \ivturns \rulet~\gbox{\leadsto E}}} \\ \\
% %%\quad\quad\quad
%   \myrule{R-IAbs}
%          {\bar{\alpha};\tenv, \rulet_1~\gbox{\leadsto x} \ivturns \rulet_2~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
%          {\bar{\alpha};\tenv \ivturns \rulet_1 \iarrow \rulet_2~\gbox{\leadsto
%             \lambda\relation{x}{||\rulet_1||}.E}} 
% \quad\quad
%   \myrule{R-TAbs}
%          {\bar{\alpha};\tenv,\alpha \ivturns \rulet~\gbox{\leadsto E}}
%          {\bar{\alpha};\tenv \ivturns \forall \alpha. \rulet~\gbox{\leadsto \Lambda\alpha.E}} 
% \\ \\
%  \myrule{R-Simp}
%         {\bar{\alpha};\tenv;\tenv \ivturns \type~\gbox{\leadsto E}}
%         {\bar{\alpha};\tenv \ivturns \type~\gbox{\leadsto E}} 
% \\ \\ \\
% \myruleform{\bar{\alpha};\tenv;\tenv' \ivturns \type~\gbox{\leadsto E}}\\ \\
% 
%   \myrule{L-RuleMatch}
%           {\tenv; \rulet~\gbox{\leadsto x} \ivturns \tau~\gbox{\leadsto E}; \overline{\rulet'~\gbox{\leadsto x}} \\
%             \bar{\alpha};\tenv \ivturns \rulet'~\gbox{\leadsto E'} \quad (\forall \rulet' \in \overline{\rulet}')
%           }
%           {\bar{\alpha};\tenv;\tenv',\rulet~\gbox{\leadsto x} \ivturns \type~\gbox{\leadsto E[\bar{E}'/\bar{x}]}} \\
%   \myrule{L-RuleNoMatch}{
% 	\mathit{stable}(\bar{\alpha},\tenv,\rulet,\type) \\
% %   \not\exists \theta, E, \Sigma, \mathit{dom}(\theta) \subseteq \bar{\alpha}: \theta(\tenv); \theta(\rulet)~\gbox{\leadsto x} \ivturns \theta(\tau)~\gbox{\leadsto E}; \Sigma \\
%            \bar{\alpha};\tenv;\tenv' \ivturns \type~\gbox{\leadsto E'}
%           }
%           {\bar{\alpha};\tenv;\tenv',\rulet~\gbox{\leadsto x} \ivturns \type~\gbox{\leadsto E'}} \\ \\
%   \myrule{L-Var}
%          {\bar{\alpha};\tenv;\tenv' \ivturns \type~\gbox{\leadsto E}
%          }
%          {\bar{\alpha};\tenv;\tenv',x:\rulet \ivturns \type~\gbox{\leadsto E}} 
% \quad\quad\quad
%   \myrule{L-TyVar}
%          {\bar{\alpha};\tenv;\tenv' \ivturns \type~\gbox{\leadsto E}
%          }
%          {\bar{\alpha};\tenv;\tenv',\alpha \ivturns \type~\gbox{\leadsto E}} 
% \\ \\ \\
% \myruleform{\tenv; \rulet~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma}\\ \\
%   \myrule{M-Simp}
%          {}
%          {\tenv; \type~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E}; \epsilon} \\ \\
%   \myrule{M-IApp}
%          {\tenv, \rulet_1 \gbox{\leadsto x}; \rulet_2 ~\gbox{\leadsto E\,x} \ivturns \type~\gbox{\leadsto E'}; \Sigma 
%           \quad\quad\quad \gbox{x~\mathit{fresh}}
%          }
%          {\tenv; \rulet_1 \iarrow \rulet_2 ~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma, \rulet_1~\gbox{\leadsto x}} \\ \\ 
%   \myrule{M-TApp}
%          {\tenv; \rulet[\suty/\alpha] ~\gbox{\leadsto E\,||\suty||} \ivturns \type~\gbox{\leadsto E'}; \Sigma
%           \quad\quad\quad
%           \tenv \turns \suty
%          }
%          {\tenv; \forall \alpha. \rulet ~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma} \\ \\ \\
% \myruleform{\mathit{stable}(\bar{\alpha},\tenv,\rulet,\type)} \\ \\
%   \myrule{Stable}{\not\exists \theta, E, \Sigma, \mathit{dom}(\theta) \subseteq \bar{\alpha}: \theta(\tenv); \theta(\rulet)~\gbox{\leadsto x} \ivturns \theta(\tau)~\gbox{\leadsto E}; \Sigma}
%           {\mathit{stable}(\bar{\alpha},\tenv,\rulet,\type)}
% \eda
% \end{minipage}
% }
% \end{center}
% }
% 
% Figure~\ref{fig:resolution2} defines the main judgement $\tenv \ivturns \rulet$ 
% in terms of three interdependent auxiliary judgements. The first of these
% auxiliary judgements is $\bar{\alpha};\tenv \ivturns \rulet$, where
% the type variables $\bar{\alpha}$ are the free type variables in the
% original environment at the point of the query. Recall the |bad| example
% from Section~\ref{sec:overview:incoherence} where there is only one such free
% type variable: |b|. 
% Tracking these free variables plays a crucial role in guaranteeing coherence
% and ensuring that resolution is stable under all type substitutions that instantiate these variables, like $[|b| \mapsto |Int|]$; how we prevent these substitutions is explained below.  The
% main judgement
% retains these free variables in rule \mylabel{R-Main} with 
% the function $\mathit{tyvars}$:
% \newcommand{\tyvars}[1]{\mathit{tyvars}(#1)}
% \begin{equation*}
% \begin{array}{rcl@@{\hspace{2cm}}rcl}
% \tyvars{\epsilon}     & = & \epsilon &
% \tyvars{\tenv,\alpha} & = & \tyvars{\tenv},\alpha \\
% \tyvars{\tenv,x : \rulet} & = & \tyvars{\tenv} &
% \tyvars{\tenv,\rulet~\gbox{\leadsto x}} & = & \tyvars{\tenv} 
% \end{array}
% \end{equation*}
% While the auxiliary judgement $\bar{\alpha};\tenv \ivturns \rulet$ extends the
% type environment $\tenv$, it does not update the type variables $\bar{\alpha}$.
% This judgement is syntax-directed on the query type $\rulet$.  Its job is to
% strip $\rulet$ down to a simple type $\type$ using literal copies of the
% ambiguous rules \mylabel{AR-TAbs} and \mylabel{AR-IAbs}, and then to hand it
% off to the second auxiliary judgement in rule \mylabel{R-Simp}.
% 
% The second auxiliary judgement, $\bar{\alpha}; \tenv; \tenv' \ivturns \type$,
% is syntax-directed on $\tenv'$: it traverses $\tenv'$ from right to left until
% it finds a rule type $\rulet$ that matches the simple type $\type$.  Rules
% \mylabel{L-Var} and \mylabel{L-TyVar} skip the irrelevant entries in the
% environment. Rule \mylabel{L-RuleMatch} identifies a matching rule type
% $\rulet$ -- where matching is determined by with the third auxiliary judgement
% -- and takes care of recursively resolving its context types; details follow
% below.  Finally, rule \mylabel{L-RuleNoMatch} skips a rule type in the
% environment if it does not match. Its condition
% $\mathit{stable}(\bar{\alpha},\tenv,\rulet,\type)$ entails the opposite of rule
% \mylabel{L-RuleMatch}'s first condition: $\not\exists
% \Sigma:~\tenv;\rulet \ivturns \type; \Sigma$.
% (We come back to the reason why the condition is stronger than this in
% Section~\ref{sec:coherence}.)
% As a consequence, rules \mylabel{L-RuleMatch} and \mylabel{L-RuleNoMatch}
% are mutually exclusive and \emph{the judgement effectively commits to the
% right-most matching rule in $\tenv'$}.
% We maintain the invariant that $\tenv'$ is a prefix of $\tenv$; rule
% \mylabel{R-Simp} provides $\tenv$ as the initial value for $\tenv'$.
% Hence, if a matching rule type $\rulet$ is found, we have that
% $\rulet \in \tenv$. Hence, the second auxiliary judgement
% plays much the same role as rule
% \mylabel{AR-IVar} in Figure~\ref{fig:resolution1}, which also selects a rule type $\rulet \in \tenv$. The difference is that rule \mylabel{AR-IVar} makes a non-deterministic
% choice, while the second auxiliary judgement makes deterministic committed choice
% that prioritises rule types more to the right in the environment. For instance, $\tyint,\tyint \vturns \tyint$ has two ways to resolve, while $\tyint,\tyint \ivturns \tyint$ has only one because the second $\tyint$ in the environment shadows the first.
% 
% 
% Finally, the third auxiliary judgement, $\tenv;\rulet \ivturns \type; \Sigma$,
% determines whether the rule type $\rulet$ matches the simple type~$\type$. The
% judgement is defined by structural induction on $\rulet$, which is step by step
% instantiated to $\type$. 
% Any recursive resolutions are deferred in this process -- the
% postponed resolvents are captured in the $\Sigma$ argument. This
% way they do not influence the matching decision and backtracking is avoided.
% Instead, the recursive resolutions are executed, as part of rule
% \mylabel{L-RuleMatch}, after the rule has been committed to.
% Rule \mylabel{M-Simp} constitutes the base case where the rule type equals the
% target type. Rule \mylabel{M-IApp} is the counterpart of the original
% rule \mylabel{R-IApp} where the implication arrow $\rulet_1 \iarrow \rulet_2$
% is instantiated to $\rulet_2$; the resolution of $\rulet_1$ is deferred.
% Lastly, rule \mylabel{M-TApp} is the counterpart of the original rule \mylabel{R-TApp}.
% The main difference is that it only uses
% monotypes $\suty$ to substitute the type variable; this implements the predicativity
% restriction explained above.
% 
% The relation to the ambiguous definition of resolution can be summarized as follows:
% if $\tenv;\rulet \ivturns \type; \bar{\rulet}$
% with
% $\tenv \vturns \rulet$ and $\tenv \vturns \bar{\rulet}$, then
% $\tenv \vturns \type$.
% 
% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
% \paragraph{Non-Ambiguity Constraints}
% 
% The rule \mylabel{M-TApp} does not explain how the substitution
% $[\suty/\alpha]$ for the rule type $\forall \alpha.\rulet$ should be obtained.
% At first sight it seems that the choice of $\suty$ is free and thus a source of
% non-determinism. However, in many cases the choice is not free at all, but is
% instead determined fully by the simple type $\type$ that we want to match.
% However, the choice is not always forced by the matching. Take for instance the context type $\forall \alpha. (\alpha \arrow \tystr)
% \iarrow (\tystr \arrow \alpha) \iarrow (\tystr \arrow \tystr)$. This 
% type encodes the well-known ambiguous Haskell type |forall a. (Show a, Read a) => String -> String| of the expression |read . show|. The
% choice of $\alpha$ is ambiguous when matching against the simple type $\tystr
% \arrow \tystr$. Yet, the choice is critical for two reasons. Firstly, if we
% guess the wrong instantiation $\suty$ for $\alpha$, then it may not be possible
% to recursively resolve $(\tystr \arrow \alpha)[\suty/\alpha]$ or $(\alpha \arrow
% \tystr)[\suty/\alpha]$, while with a lucky guess both can be resolved.
% Secondly, for different choices of $\suty$ the types $(\tystr \arrow
% \alpha)[\suty/\alpha]$ and $(\alpha \arrow \tystr)[\suty/\alpha]$ can be resolved
% in completely different ways.
% 
% In order to avoid any problems, we conservatively forbid all ambiguous context
% types in the implicit environment with the $\unamb \rulet_1$
% side-condition in rule \mylabel{Ty-IAbs} of Figure~\ref{fig:type}.\footnote{An
% alternative design to avoid such ambiguity would instantiate unused type
% variables to a dummy type, like GHC's \texttt{GHC.Prim.Any}, which is only used
% for this purpose.} This judgement is defined in Figure~\ref{fig:unamb}
% in terms of the auxiliary judgement $\bar{\alpha} \unamb \rulet$ which
% takes an additional sequence of type variables $\alpha$ that is initially
% empty.
% \figtwocol{fig:unamb}{Unambiguous Context Types}{
% \begin{center}
% \framebox{
% \begin{minipage}{0.969\textwidth}
% \bda{c}
% \myruleform{\unamb \rulet} 
% \quad\quad\quad
% \myrule{UA-Main}
%        {\epsilon \unamb \rulet}
%        {\unamb \rulet}
% \\ \\
% \myruleform{\bar{\alpha} \unamb \rulet} 
% \quad\quad\quad
% \myrule{UA-Simp}
%        {\bar{\alpha} \subseteq \mathit{ftv}(\type)}
%        {\bar{\alpha} \unamb \type}
% \\ \\
% \myrule{UA-TAbs}
%        {\bar{\alpha},\alpha \unamb \rulet}
%        {\bar{\alpha} \unamb \forall \alpha.\rulet} 
% \quad\quad\quad
% \myrule{UA-IAbs}
%        {\unamb \rulet_1 \quad\quad \bar{\alpha} \unamb \rulet_2}
%        {\bar{\alpha} \unamb \rulet_1 \iarrow \rulet_2} \\ \\
% % \mylabel{UA-TAbsAlt} \quad
% % \myirule{\bar{\alpha} \vdash_{\mathit{unamb}} \rulet}
% %         {\bar{\alpha} \vdash_{\mathit{unamb}} \forall \alpha.\rulet}
% % \quad\quad\quad
% % \mylabel{UA-IAbsAlt} \quad
% % \myirule{\epsilon \vdash_{\mathit{unamb}} \rulet_1 \quad\quad \bar{\alpha},\mathit{ftv}(\rulet_1) \vdash_{\mathit{unamb}} \rulet_2}
% %         {\bar{\alpha} \vdash_{\mathit{unamb}} \rulet_1 \iarrow \rulet_2} \\ \\
% \eda
% \end{minipage}
% }
% \end{center}
% }
% 
% The auxiliary judgement expresses that all type variables $\bar{\alpha}$ 
% are resolved when matching against $\rulet$.
% Its base case, rule \mylabel{UA-Simp}, expresses
% that fixing the simple type $\type$ also fixes the type variables
% $\bar{\alpha}$. Inductive rule \mylabel{UA-TAbs}
% accumulates the bound type variables $\bar{\alpha}$ before the
% head. Rule \mylabel{UA-IAbs} skips over any contexts
% on the way to the head, but also recursively requires that these contexts are
% unambiguous. 
% 
% Finally, the unambiguity condition is imposed on the queried type $\rulet$
% in rule \mylabel{Ty-Query} because this type too may extend the implicit
% environment in rule \mylabel{R-IAbs}.
% 
% Note that the definition rules out harmless ambiguity, such as that in the type
% $\forall \alpha. \tyint$. When we match the head of this type $\tyint$ with the
% simple type $\tyint$, the matching succeeds without actually determining how
% the type variable $\alpha$ should be instantiated. Here the ambiguity is
% harmless, because it does not affect the semantics. Yet, for the sake of
% simplicity, we have opted to not differentiate between harmless and harmful
% ambiguity.
% 
% %-------------------------------------------------------------------------------
% \paragraph{Coherence Enforcement}\label{sec:coherence}
% 
% In order to enforce coherence, rule \mylabel{L-RuleNoMatch} makes sure that the
% decision to not select a context type is stable under all possible
% substitutions $\theta$.  Consider for instance the |bad| example from Section~\ref{sec:overview:incoherence}: when looking up |b -> b|, the rule 
% |Int -> Int| does not match and is otherwise skipped. Yet, under the substitution
% $\theta = [|b| \mapsto |Int|]$ the rule would match after all. In
% order to avoid this unstable situation, rule \mylabel{L-RuleNoMatch} only skips a context
% type in the implicit environment, if there is no substitution $\theta$ for
% which the type would match the context type.
% 
% This approach is similar to the treatment of overlapping type class instances
% or overlapping type family instances in Haskell. However, there is one
% important complicating factor here: the query type may contain universal
% quantifiers.  Consider a query for |forall a. a -> a|. In this case we wish to
% rule out entirely the context type |Int -> Int| as a potential match. Even
% though it matches under the substitution $\theta = [|a| \mapsto |Int|]$,
% that covers only one instantiation while the query clearly requires a resolvent that
% covers all possible instantiations.
% 
% We clearly identify which type variables $\bar{\alpha}$ are to be considered
% for substitution by rule \mylabel{L-RuleNoMatch} by parametrising the
% judgements by this set. These are the type variables that occur in the environment
% $\tenv$ at the point of the query. The main resolution judgement $\ivturns \rulet$
% grabs them and passes them on to all uses of rule \mylabel{L-RuleNoMatch}.

%===============================================================================
\section{Resolution Algorithm}

\newcommand{\alg}{\turns_{\mathit{alg}}}
\newcommand{\coh}{\turns_{\mathit{coh}}}
\newcommand{\mgu}[3][\bar{\alpha}]{\textit{unify}_{\tenv;#1}(#2,#3)}
\newcommand{\mgun}[4][\tenv]{\textit{unify'}_{#2}(#3,#4)}

This section presents in Figure~\ref{fig:algorithm} an algorithm that implements the
deterministic resolution rules of Figure~\ref{fig:resolution2}.
It differs from the latter in two important ways: 
firstly, it computes rather than guesses type substitutions in rule
\mylabel{M-TApp}; 
and secondly,
it replaces explicit quantification over all substitutions $\theta$ in rule
\mylabel{Stable} with a tractable approach to coherence checking.

The definition of the algorithm is structured in the same way
as the declarative specification: with one main judgement and three
auxiliary ones that have similar roles. In fact, since the differences
are not situated in the main and first auxiliary judgement, these are
actually identical.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\subsection{Deferred Variable Instantiation}
The first difference is situated in the third
auxiliary judgement $\bar{\alpha};\tenv;\rulet;\Sigma \alg \type ; \Sigma'$.
While its declarative counterpart immediately instantiates the quantified type
variable in Rule~\mylabel{M-TApp}, this algorithmic formulation defers the
instantiation to the point where a deterministic choice can be made. As long as
the type variables $\bar{\alpha}$ have not been instantiated, the judgement
keeps track of them in its first argument. The actual instantiation happens in
the base case, Rule \mylabel{Alg-M-Simp}. This last rule performs the deferred
instantiation of type variables $\bar{\alpha}$ by computing the \emph{most
general unifier} $\theta = \mgu{\type'}{\type}$. The unification
algorithm, which we present below, computes a substitution
$\theta$ that is valid (i.e., $\bar{\alpha}; \tenv \vdash \theta$) and
that equates the two types (i.e., $\theta(\type) = \theta(\type')$).

In order to subject the recursive goals to this
substitution, the algorithmic judgement
makes use of an accumulating parameter $\Sigma$.  This accumulator $\Sigma$
represents all the goals collected so far in which type variables
have not been substituted yet. In contrast, $\Sigma'$ denotes all obligations
with type variables already substituted.

Finally, observe that rule \mylabel{Alg-L-RuleMatch} invokes the algorithmic
judgement with an empty set of not-yet-instantiated type variables and an empty
accumulator $\Sigma$.

The following example illustrates the differences between the declarative
judgement:
\bda{c}
  \inferrule*[Right=\mylabel{M-TApp}]
    {\inferrule*[Right=\mylabel{M-IApp}]
       {\inferrule*[Right=\mylabel{M-Simp}]
           {}
           {\tenv; [\tyint]~\gbox{\leadsto x\,\tyint\,y} \vdash \tyint ~\gbox{\leadsto x\,\tyint\,y}; \epsilon}
       }
       {\tenv; [\tyint \iarrow \tyint]~\gbox{\leadsto x\,\tyint} \ivturns \tyint ~\gbox{\leadsto x\,\tyint\,y}; \tyint ~\gbox{\leadsto y}}
    }
    {\tenv; [\forall \alpha. \alpha \iarrow \alpha]~\gbox{\leadsto x} \ivturns \tyint ~\gbox{\leadsto x\,\tyint\,y}; \tyint ~\gbox{\leadsto y}}
\eda
and its algorithmic counterpart:
\bda{c}
  \inferrule*[Right=\mylabel{Alg-M-TApp}]
    {\inferrule*[Right=\mylabel{Alg-M-IApp}]
       {\inferrule*[Right=\mylabel{Alg-M-Simp}]
           {[\tyint/\alpha] = \mgu[\alpha]{\alpha}{\tyint}}
           {\alpha; \tenv; [\alpha]~\gbox{\leadsto x\,\alpha\,y}; \alpha~\gbox{\leadsto y} \vdash \tyint ~\gbox{\leadsto x\,\tyint\,y}; \epsilon}
       }
       {\alpha; \tenv; [\alpha \iarrow \alpha]~\gbox{\leadsto x\,\alpha}; \epsilon \ivturns \tyint ~\gbox{\leadsto x\,\tyint\,y}; \tyint ~\gbox{\leadsto y}}
    }
    {\epsilon; \tenv; [\forall \alpha. \alpha \iarrow \alpha]~\gbox{\leadsto x}; \epsilon \ivturns \tyint ~\gbox{\leadsto x\,\tyint\,y}; \tyint ~\gbox{\leadsto y}}
\eda

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\subsection{Algorithmic Stability Check}

The second difference can be found in the second judgement's Rule \mylabel{Alg-L-RuleNoMatch}. Instead of
using the $\mathit{stable}(\bar{\alpha},\tenv,\rulet~\gbox{\leadsto x},\type)$ judgement, which quantifies over all valid 
substitutions, this rule uses the algorithmic judgement
$\bar{\alpha};\tenv;\rulet\coh\type$. This auxiliary judgement checks algorithmically
whether the context type $\rulet$ matches $\type$ under any possible instantiation
of the type variables $\bar{\alpha}$.

We apply the same deferred-instantation technique as with the first difference: Instead,
of applying a substitution first and then checking whether the rule matches the goal, we 
defer the instantiation to the end where we can deterministically pick one instantiation instad of considering all valid instantiations. 
As a consequence of the similarity, 
the definition of the judgement $\bar{\alpha};\tenv;\rulet \coh \type$ is a
variation on that of $\bar{\alpha}; \tenv; \rulet~\gbox{\leadsto
E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'$.

There are two differences. Firstly, since the judgement is only concerned with
matchability, no recursive resolvents $\Sigma$ are collected nor are any
elaborations tracked.
Secondly, since the coherence check considers the substitution of the type
variables $\bar{\alpha}$ that occur in the environment at the point of the
query, rule \mylabel{Alg-L-RuleNoMatch} pre-populates the substitutable
variables of the $\coh$ judgement with them. Contrast this with the matching
judgement where only the rule's quantified variables are instantiated.

%-------------------------------------------------------------------------------
\subsection{Scope-Aware Unification}

The unification algorithm $\theta= \mgu{\rulet_1}{\rulet_2}$ is
a key component of the two algorithmic changes explained above.

Figure~\ref{fig:mgu} provides its definition, which is an extension of standard
first-order unification~\cite{martellimonatanari}. The domain restriction
$\bar{\alpha}$ denotes which type variables are to be treated as unification
variables; all other type variables are to be treated as constants. The returned
substitution is 
a unifier of $\rulet_1$ and $\rulet_2$, i.e., $\theta(\rulet_1) = \theta(\rulet_2)$.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Validity}
The differences with standard first-order unification arise because the
algorithm has to account for the scope of type variables. Indeed, as we have already
explained in Section~\ref{subsec:det}, we expect that the returned substitution
is valid, i.e., $\bar{\alpha};\tenv \vdash \theta$.
For instance, using standard first-order unification for $\mgu[\beta]{\forall
\alpha. \alpha \to \beta}{\forall \alpha.\alpha \to \alpha}$ would yield the
\emph{invalid}
substitution $[\beta/\alpha]$. The substitution is invalid because
$\alpha$ is not in scope in $\tenv$.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Most General Unifier}
Secondly, traditional unification computes the most general unifier, i.e., any other
unifier can be expressed as its composition with another substitution.
Yet, the most general unifier may not be a valid substitution, while more
specific unifiers may be valid.  Consider for instance unifying $\alpha$ with
$\beta \arrow \beta$ where $\tenv = \alpha, \beta$ and both $\alpha$ and
$\beta$ are unification variables. The most general unifier is obviously
$[\beta \arrow \beta/\alpha]$. However this unifier is clearly not valid, as
$\alpha$ apears before $\beta$ in the environment. In contrast, there are
infinitely many more specific unifiers that are valid, all of the form
$[\rulet\arrow\rulet/\alpha,\rulet/\beta]$ where $\rulet$ is a closed type.

Fortunately, by a stroke of luck, the above is not a problem for either
of our two use cases:
\begin{itemize}
\item
The first use case is that in Rule~\mylabel{Alg-M-Simp} where this is not a
problem because the scenario never arises. In
$\mgu{\type'}{\type}$ only $\type'$ contains unification
variables and hence the range of the substitution never contains any
unification variables. As a consequence the above exampe and others like
it cannot occur.
\item
The second use case, in Rule~\mylabel{Coh-Simp}, is
only interested in the existence of a valid substitution. We neither care
which one it is nor whether it is the most general one. Moreover, as
illustrated above, whenever there is a most general substitution that is invalid
due to the relative position of unification variables in the environment, we
can always construct a more specific valid substitution by substituting the remaining
unification variables by closed types.
\end{itemize}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Definition}

With the above issues in mind we can consider the actual definition in
Figure~\ref{fig:algorithm}. The main unification judgement $\theta =
\mgu{\rulet_1}{\rulet_2}$ is defined by Rule~\mylabel{U-Main}. This rule
computes the unifier in terms of the auxiliary judgement $\theta =
\mgun{\bar{\alpha}}{\rulet_1}{\rulet_2}$, which is essentially standard
unification, and then checks the above vality concerns.  Indeed, for any type
variable $\beta$ that appears in the image of a type variable $\alpha$, either
$\beta$ must appear before $\alpha$ in the environment $\tenv$ (regular
validity), or $\beta$ must itself be a unification variable (the exceptional
case). The relative position of variables is checked with 
the auxiliary judgement $\beta >_\tenv \alpha$ whose one rule verifies
that $\beta$ appears before $\alpha$ in the environment $\tenv$.\footnote{If
type variables are represented by de Bruijn indices, this can be done by
checking whether one index is greater than the other.}

The auxiliary judgement $\mgun{\bar{\alpha}}{\rulet_1}{\rulet_2}$ computes the
actual unifier. 
Rule \mylabel{U-Var} is the standard reflexivity rule for type variables. 
Rules \mylabel{U-InstL} and \mylabel{U-InstR} are two
symmetric base cases; they only create a substitution $[\suty/\alpha]$ if
$\alpha$ is one of the unification variables and if $\alpha$ does not occur in $\suty$, which is
the well-known occurs-check.
Rules \mylabel{U-Fun}
\mylabel{U-Rul} and \mylabel{U-Univ} are standard congruence rules that combine the
unifications derived for their subterms.

% \paragraph{Ambiguity}
% Some of the type variables $\bar{\alpha}$ may not be instantiated by the
% matching unifier $\theta$ because they do not appear in $\tau'$. This situation
% arises for types like $\forall \alpha.\tyint$.  In order not to introduce any
% unbound type variables, \mylabel{MTC-Simp} rejects this situation by requiring
% that the domain of $\theta$ exactly coincides with $\bar{\alpha}$.
% 
% An alternative design would be to instantiate the unbound type variables to a
% dummy type, like GHC's \texttt{GHC.Prim.Any}, which is only used for this purpose.

\figtwocol{fig:algorithm}{Resolution Algorithm}{
\begin{center}
\framebox{\scriptsize
\begin{minipage}{0.969\textwidth}
\bda{c}
\myruleform{\tenv \alg \rulet~\gbox{\leadsto E}} \\ \\

\myrule{Alg-R-Main}{\mathit{tyvars}(\tenv);\tenv \alg \rulet~\gbox{\leadsto E}}
        {\tenv \alg \rulet~\gbox{\leadsto E}}  \\ \\

\myruleform{\bar{\alpha};\tenv \alg \rulet~\gbox{\leadsto E}}  \\ \\

\myrule{Alg-R-IAbs}{\bar{\alpha};\tenv, \rulet_1~\gbox{\leadsto x} \alg \rulet_2~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
        {\bar{\alpha};\tenv \alg \rulet_1 \iarrow \rulet_2 ~\gbox{\leadsto \lambda(x : ||\rulet_1||). E}} \quad\enskip

\myrule{Alg-R-TAbs}{\bar{\alpha};\tenv,\alpha \alg \rulet ~\gbox{\leadsto E}}
        {\bar{\alpha};\tenv \alg \forall \alpha. \rulet ~\gbox{\leadsto \Lambda \alpha. E}}  \\ \\

\myrule{Alg-R-Simp}{\bar{\alpha};\tenv;\tenv \alg \tau~\gbox{\leadsto E}}
        {\bar{\alpha};\tenv \alg \tau ~\gbox{\leadsto E} }  \\ \\


% \mylabel{Alg-Simp}\quad
% \myirule{\bar{\alpha};\tenv \turns_{\mathit{match1st}} \tau \hookrightarrow \bar{\rulet}\gbox{; \bar{\omega}; E} \quad\quad \bar{\alpha};\tenv \alg \rulet_i~\gbox{\leadsto E_i} \quad (\forall \rulet_i \in \bar{\rulet})}
%         {\bar{\alpha};\tenv \alg \tau ~\gbox{\leadsto E[\bar{\omega}/\bar{E}]} }  \\ \\

\multicolumn{1}{c}{\myruleform{\bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E} }} \\ \\

\myrule{Alg-L-RuleMatch}{\epsilon; \tenv; \rulet~\gbox{\leadsto x}; \epsilon \alg \type~\gbox{\leadsto E}; \bar{\rulet}'~\gbox{\leadsto \bar{x}'} \quad\quad
         \bar{\alpha};\tenv \alg \rulet'~\gbox{\leadsto E'} \quad (\forall \rulet' \in \bar{\rulet}')
        }
        {\bar{\alpha};\tenv; \tenv', \rulet~\gbox{\leadsto x} \alg \type~\gbox{\leadsto E[\bar{E}'/\bar{x}'] }}  \\ \\

\myrule{Alg-L-RuleNoMatch}{\bar{\alpha};\tenv;\rulet \not\coh \type \quad\quad
         \bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E'}}
        {\bar{\alpha};\tenv;\tenv', \rulet~\gbox{\leadsto x}\alg \type~\gbox{\leadsto E'}}  \\ \\
  \myrule{Alg-L-Var}{\bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E}
          }
          {\bar{\alpha};\tenv;\tenv',x:\rulet \alg \type~\gbox{\leadsto E}} 
\quad\quad\quad
  \myrule{Alg-L-TyVar}{\bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E}
          }
          {\bar{\alpha};\tenv;\tenv',\alpha \alg \type~\gbox{\leadsto E}} 
\\ \\

\multicolumn{1}{c}{\myruleform{\bar{\alpha}; \tenv; \rulet~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}} \\ \\

\myrule{Alg-M-Simp}{\theta = \mgu{\type}{\type'}
        }
        {\bar{\alpha}; \tenv; \type'~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto ||\theta||(E)}; \theta(\Sigma)}  \\ \\

\myrule{Alg-M-IApp}{\bar{\alpha}; \tenv, \rulet_1~\gbox{\leadsto x}; \rulet_2~\gbox{\leadsto E\,x}; \rulet_1~\gbox{\leadsto x}, \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'\quad\quad \gbox{x~\mathit{fresh}}}
        {\bar{\alpha}; \tenv; \rulet_1 \iarrow \rulet_2~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}  \\ \\

\myrule{Alg-M-TApp}{\bar{\alpha},\alpha; \tenv,\alpha; \rulet~\gbox{\leadsto E\,\alpha}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}
        {\bar{\alpha}; \tenv; \forall \alpha. \rulet~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'} 
\\ \\
\myruleform{\bar{\alpha};\tenv;\rulet\coh \tau} \\ \\
\myrule{Coh-TApp}{\bar{\alpha},\alpha;\tenv,\alpha;\rulet \coh \tau}
        {\bar{\alpha};\tenv;\forall \alpha. \rulet\coh \tau}  
\quad\quad\quad
\myrule{Coh-IApp}{\bar{\alpha};\tenv;\rulet_2 \coh \tau}
        {\bar{\alpha};\tenv;\rulet_1 \iarrow \rulet_2\coh \tau} \\ \\
\myrule{Coh-Simp}{\theta = \mgu{\tau}{\tau'}
        }
        {\bar{\alpha};\tenv;\tau'\coh \tau}  
\eda
\end{minipage}
}
\end{center}
}

\figtwocol{fig:mgu}{Unification Algorithm}{
\begin{center}
\framebox{\scriptsize
\begin{minipage}{0.969\textwidth}
\bda{c}
% \multicolumn{1}{c}{\myruleform{\theta = \mathit{mgu}_{\bar{\alpha}}(\rulet_1,\rulet_2)}} \\ \\
% \mylabel{U-InstL}\quad\myirule{ \alpha \in \bar{\alpha}
%         } 
%         { [\suty/\alpha] = \mathit{mgu}_{\bar{\alpha}}(\alpha,\suty)} \hspace{1cm} 
% 
% \mylabel{U-InstR}\quad\myirule{ \alpha \in \bar{\alpha}
%         } 
%         { [\suty/\alpha] = \mathit{mgu}_{\bar{\alpha}}(\suty,\alpha)} \\ \\
% 
% \mylabel{U-Var}\quad
% \myirule{
%         } 
%         { \epsilon = \mathit{mgu}_{\bar{\alpha}}(\beta,\beta)}  \\ \\
% 
% \mylabel{U-Fun}\quad
% \myirule{\theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rulet_{1,1},\rulet_{2,1})
%          \quad\quad
%          \theta_2 = \mathit{mgu}_{\bar{\alpha}}(\theta_1(\rulet_{1,2}),\theta_1(\rulet_{2,2}))
%         } 
%         {\theta_2 \cdot \theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rulet_{1,1} \arrow \rulet_{1,2},\rulet_{2,1} \arrow \rulet_{2,2})}  \\ \\
% 
% 
% \mylabel{U-Rul}\quad
% \myirule{\theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rulet_{1,1},\rulet_{2,1})
%          \quad\quad
%          \theta_2 = \mathit{mgu}_{\bar{\alpha}}(\theta_1(\rulet_{1,2}),\theta_1(\rulet_{2,2}))
%         } 
%         {\theta_2 \cdot \theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rulet_{1,1} \iarrow \rulet_{1,2},\rulet_{2,1} \iarrow \rulet_{2,2})}  \\ \\
% 
% \mylabel{U-Univ}\quad
% \myirule{\theta = \mathit{mgu}_{\bar{\alpha}}(\rulet_{1},\rulet_{2})
%           \quad\quad
%           \beta \not\in \mathit{ftv}(\theta)
%         } 
%         {\theta = \mathit{mgu}_{\bar{\alpha}}(\forall \beta.\rulet_{1},\forall \beta.\rulet_{2})}  \\ \\

\myruleform{\theta = \mgu{\rulet_1}{\rulet_2}} \\ \\

\myrule{U-Main}{ 
           \theta = \mgun{\bar{\alpha}}{\rulet_1}{\rulet_2}\\
	   \beta \in \bar{\alpha} \vee \beta >_\tenv \alpha \quad(\forall [\suty/\alpha] \in \theta, \forall \beta \in \mathit{ftv}(\suty))
        } 
        { \theta = \mgu{\rulet_1}{\rulet_2}}  \\ \\

\myruleform{\theta = \mgun{\bar{\alpha}}{\rulet_1}{\rulet_2}} \\ \\

\myrule{U-Var}{
        } 
        { \epsilon = \mgun{\bar{\alpha}}{\beta}{\beta}}  \\


\myrule{U-InstL}{ 
	  \alpha \in \bar{\alpha} \\ \alpha \not\in \mathit{ftv}(\suty)
        } 
        { [\suty/\alpha] = \mgun{\bar{\alpha}}{\alpha}{\suty}}  \qquad

\myrule{U-InstR}{ 
	  \alpha \in \bar{\alpha} \\ \alpha \not\in \mathit{ftv}(\suty)
        } 
        { [\suty/\alpha] = \mgun{\bar{\alpha}}{\suty}{\alpha}} \\ \\

\myrule{U-Fun}{\theta_1 = \mgun{\bar{\alpha}}{\rulet_{11}}{\rulet_{21}}
         \quad\quad
         \theta_2 = \mgun{\bar{\alpha}}{\theta_1(\rulet_{12})}{\theta_1(\rulet_{22})}
        } 
        {\theta_2 \cdot \theta_1 = \mgun{\bar{\alpha}}{\rulet_{11} \arrow \rulet_{12}}{\rulet_{21} \arrow \rulet_{22}}}  \\ \\


\myrule{U-Rul}{\theta_1 = \mgun{\bar{\alpha}}{\rulet_{11}}{\rulet_{21}}
         \quad\quad
         \theta_2 = \mgun{\bar{\alpha}}{\theta_1(\rulet_{12})}{\theta_1(\rulet_{22})}
        } 
        {\theta_2 \cdot \theta_1 = \mgun{\bar{\alpha}}{\rulet_{11} \iarrow \rulet_{12}}{\rulet_{21} \iarrow \rulet_{22}}}  \\ \\

\myrule{U-Univ}{\theta = \mgun[\tenv,\beta]{\bar{\alpha}}{\rulet_{1}}{\rulet_{2}}
        } 
        {\theta = \mgun{\bar{\alpha}}{\forall \beta.\rulet_{1}}{\forall \beta.\rulet_{2}}}  \\ \\

\myruleform{\beta >_\tenv \alpha}
\hspace{1cm}
\myirule{
}
{ \beta >_{\tenv_1,\beta,\tenv_2,\alpha,\tenv_3} \alpha }

\eda
\end{minipage}
}
\end{center}
}

%===============================================================================

%-------------------------------------------------------------------------------
\subsection{Termination of Resolution}

\newcommand{\term}[1]{\turns_\mathit{term} #1}
\newcommand{\occ}[2]{\mathit{occ}_{#1}(#2)}
\newcommand{\tnorm}[1][\cdot]{\||#1\||}

If we are not careful about which rules are added to the implicit environment,
then the resolution process may not terminate.  This section describes how to
impose a set of modular syntactic restrictions that prevents non-termination. 
As an example of non-termination consider 
\begin{equation*}
  \tychar \To \tyint,
  \tyint \To \tychar \vturns \tyint
\end{equation*}
which loops, using alternatively the first and second rule in the
environment. The source of this non-termination is the recursive 
nature of resolution: a simple type can be resolved
in terms of a rule type whose head it matches, but this requires further 
resolution of the rule type's context. 

The problem of non-termination has been widely studied in the context of
Haskell's type classes, and a set of modular syntactic restrictions
has been imposed on type class instances to avoid non-termination~\cite{fdchr}. 
This paper adapts those restrictions to the setting of \name.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Overall Approach}

We show termination by characterising the resolution process as a (resolution)
tree with goals in the nodes. The initial goal sits at the root of the tree. A
multi-edge from a parent node to its children presents a rule from the
environment that matches the parent node’s goal; the nodes children are the
recursive goals. 

Resolution terminates if the tree is finite.  Hence, if it does not terminate,
there is an infinite path from the root in the tree, that denotes an infinite
sequence of matching rule applications. To show that there cannot be such an
infinite path, we use a norm $\tnorm$ (defined at the bottom of Figure~\ref{fig:termination})
that maps the head of every goal $\rulet$ to a natural number, its size.

If we can show that this size strictly decreases from any parent goal to its
children, then we know that, because the order on the natural numbers is
well-founded, on any path from the root there is evantually a goal that has no
children.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Termination Condition}
It is trivial to show that the size strictly decreases, if we require that
every rule in the environment makes it so. This requirement is formalised as
 the termination condition $\term{\rulet}$ in Figure~\ref{fig:termination}.

The judgement is defined by case analysis on the type $\rulet$. Rule~\mylabel{T-Simp} states that simple types trivially satisfy the
condition. Next, Rule \mylabel{T-Forall} is the obvious congruence rule for
universally quantified types. Finally, Rule~\mylabel{T-Rule} enforces
the actual condition on rule types $\rulet_1 \iarrow \rulet_2$, which
requires that the head $\type_1$ of $\rulet_1$ is strictly smaller than the
head $\type_2$ $\rulet_2$.
In addition, the rule ensures that this property is stable
under type substitution. Consider for instance the type
$\forall a. (a \arrow a) \iarrow (a \arrow \mathit{Int} \arrow \tyint)$. 
The head's size 5 is strictly greater than the context
constraint's size 3. Yet, if we instantiate $\alpha$ to
$(\tyint \arrow \tyint \arrow \tyint)$, 
then the
head's size becomes 10 while the context constraint's size becomes 11.

Declaratively, we can formulate stability as: 
\[\forall \theta.
\mathit{dom}(\theta) \subseteq \mathit{ftv}(\rulet_1) \cup \mathit(ftv)(\rulet_2): 
\enskip \tnorm[\theta(\rulet_1)] <
\tnorm[\theta(\rulet_2)]\]
Instead of enumerating all possible substitutions, Rule~\mylabel{T-Rule} uses instead an
equivalent algorithmic formulation which states that the number of occurrences
of any free type variable $\alpha$ may not be larger in $\rulet_1$ than in
$\rulet_2$. The auxiliary function $\occ{\alpha}{\rulet}$ is used here to
determine the number of occurrences of $\alpha$ in $\rulet$.

Finally, as the types have a recursive structure whereby their components are
themselves added to the environment, Rule~\mylabel{T-Rule} also enforces the
termination condition recursively on the components.

\figtwocol{fig:termination}{Termination Condition}{
\begin{center}
\framebox{\scriptsize
\begin{minipage}{.969\textwidth}
\begin{equation*}
\ba{c}
\myruleform{\term{\rulet}}
\quad\quad\quad
  \myrule{T-Simp}{}
          {\term{\tau}} 
\quad\quad\quad
  \myrule{T-Forall}{\term{\rulet}}
          {\term{\forall \alpha. \rulet}} 
\\ \\
  \myrule{T-Rule}{\term{\rulet_1} \quad\quad \term{\rulet_2} \quad\quad
           \tau_1 = \head{\rulet_1} \quad\quad \tau_2 = \head{\rulet_2} \\ \tnorm[\tau_1] < \tnorm[\tau_2] \\
           \forall \alpha \in \ftv{\rulet_1} \cup \ftv{\rulet_2}: \; \occ{\alpha}{\tau_1} \leq \occ{\alpha}{\tau_2}}  
          {\term{\rulet_1 \iarrow \rulet_2}} 
  \\ \\
\ea
\end{equation*}
\begin{equation*}
    \ba{rcl@@{\hspace{7mm}}rcl@@{\hspace{7mm}}rcl}
      \head{\type} & = & \type &
      \head{\forall \alpha.\rulet} & = & \head{\rulet} &
      \head{\rulet_1 \iarrow \rulet_2} & = & \head{\rulet_2}
      \\ \\
    \ea
\end{equation*}
\begin{equation*}
    \ba{rcl@@{\hspace{7mm}}rcl}
      \occ{\alpha}{\beta} & = & \left\{ \begin{array}{ll} 
         1 & \hspace{1cm}(\alpha = \beta) \\
         0 & \hspace{1cm}(\alpha \neq \beta)
         \end{array}\right. &
      \occ{\alpha}{\forall \beta.\rulet} & = & \occ{\alpha}{\rulet} \quad (\alpha \neq \beta)  \\
      \occ{\alpha}{\rulet_1 \arrow \rulet_2} & = & \occ{\alpha}{\rulet_1} + \occ{\alpha}{\rulet_2} &
      \occ{\alpha}{\rulet_1 \iarrow \rulet_2} & = & \occ{\alpha}{\rulet_1} + \occ{\alpha}{\rulet_2} 
      \\ \\
      \tnorm[\alpha] & = & 1 &
      \tnorm[\forall \alpha.\rulet] & = & \tnorm[\rulet] \\
      \tnorm[\rulet_1 \arrow \rulet_2] & = & 1 + \tnorm[\rulet_1] + \tnorm[\rulet_2] &
      \tnorm[\rulet_1 \iarrow \rulet_2] & = & 1 + \tnorm[\rulet_1] + \tnorm[\rulet_2] 
    \ea
\end{equation*}
\end{minipage}
}
\end{center}
}

% \defterm

% Haskell's condition is quite severe because the one global scope for all type
% class instances is \textit{open}: more instances can be added later (in other
% modules).  The modularity of the condition already anticipates such future
% additions.
% 
% In contrast, our local scopes are \textit{closed}. Later extensions of the
% program (e.g., new modules) do not affect the existing scopes. Hence, in
% $\name$, termination of resolution coincides with the traditional program
% termination problem. So, alternatively, $\name$  may enforce termination in
% a less stringent manner using available termination checkers like~\cite{approve}.

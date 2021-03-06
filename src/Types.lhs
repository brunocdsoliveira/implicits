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
\framebox{
\begin{minipage}{\textwidth}
\bda{c}
\multicolumn{1}{c}{\myruleform{\tenv \turns \rulet}} \\ \\

\WFVarTy \quad
  \myirule{ \alpha \in \tenv }
          { \tenv \turns \alpha } \quad\quad\quad
\WFFunTy \quad
  \myirule{\tenv \turns \rulet_1 \quad\quad \tenv \turns \rulet_2}
          {\tenv \turns \rulet_1 \arrow \rulet_2} \\ \\
\WFAbsTy \quad
  \myirule{ \tenv, \alpha \turns \rulet}
          { \tenv \turns \forall\alpha.\rulet } \quad\quad\quad
\WFRulTy \quad
  \myirule{\tenv \turns \rulet_1 \quad\quad \tenv \turns \rulet_2}
          {\tenv \turns \rulet_1 \iarrow \rulet_2}
\eda

\bda{lc} 

& \multicolumn{1}{c}{
  \myruleform{\tenv \turns \relation{e}{\rulet}~\gbox{\leadsto E}}} \\
\\

\TyVar &
\myirule
{ (\relation{x}{\rulet}) \in \tenv}
{ \tenv \turns \relation{x}{\rulet}~\gbox{\leadsto x}
} 
\\ \\

\TyAbs &
\myirule
{ \tenv,\relation{x}{\rulet_1} \turns \relation{e}{\rulet_2}~\gbox{\leadsto E}
  \quad\quad\quad \tenv \turns \rulet_1 
}
{ \tenv \turns \relation{\lambda \relation{x}{\rulet_1}.e}{\rulet_1 \arrow \rulet_2}
  ~\gbox{\leadsto \lambda \relation{x}{||\rulet_1||}.E} } 
\\ \\

\TyApp &
\myirule
{ \tenv \turns \relation{e_1}{\rulet_1 \arrow \rulet_2}~\gbox{\leadsto E_1} 
  \quad\quad\quad
  \tenv \turns \relation{e_2}{\rulet_1}~\gbox{\leadsto E_2}
}
{ \tenv \turns \relation{e_1\,e_2}{\rulet_2}~\gbox{\leadsto E_1\,E_2}} 
\\ \\

\TyTAbs&
  \myirule {  \tenv,\alpha \turns \relation{e}{\rulet}~\gbox{\leadsto E_1} 
           }
           { \tenv \turns \relation{\Lambda \alpha.e}{\forall
               \alpha.\rulet}~\gbox{\leadsto \Lambda \alpha.E_1} }
\\ \\
\TyTApp&
  \myirule { \tenv \turns \relation{e}{\forall \alpha.\rulet_2}~\gbox{\leadsto E}
              \quad\quad\quad
              \tenv \turns \rulet_1 
           }
           { \tenv \turns \relation{e\,\rulet_1}{\rulet_2 [\rulet_1 /\alpha]}~\gbox{\leadsto
    E~||\rulet_1||}} 
\\ \\
\TyIAbs&
  \myirule { \tenv, \rulet_1 \gbox{\leadsto x} \turns \relation{e}{\rulet_2}~\gbox{\leadsto
    E} 
             \quad \tenv \turns \rulet_1 
             \quad \unamb \rulet_1
             \quad \gbox{x~\mathit{fresh}}}
           { \tenv \turns \relation{\ilambda \rulet_1.e}{\rulet_1 \iarrow \rulet_2}~\gbox{\leadsto
    \lambda \relation{x}{||\rulet_1||}. E}}
\\ \\
\TyIApp&
  \myirule { \tenv \turns \relation{e_1}{\rulet_2 \iarrow
      \rulet_1~\gbox{\leadsto E_1}} 
             \quad\quad\quad
             \tenv \turns \relation{e_2}{\rulet_2}~\gbox{\leadsto E_2}}
           { \tenv \turns \relation{e_1 \with e_2}{\rulet_1}~\gbox{\leadsto
    E_1~E_2}}
\\ \\
\TyQuery &
\myirule
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
\framebox{$
\ba{c}
\myruleform{\tenv \vturns \rulet~\gbox{\leadsto E}}
\quad\quad\quad
\mylabel{AR-IVar} \quad
  \myirule{\rulet~\gbox{\leadsto x} \in \tenv}
          {\tenv \vturns \rulet~\gbox{\leadsto x}}
\\ \\
\mylabel{AR-TAbs} \quad
  \myirule{\tenv, \alpha \vturns \rulet~\gbox{\leadsto E}}
          {\tenv \vturns \forall \alpha. \rulet~\gbox{\leadsto \Lambda\alpha.E}} 
\quad\quad\quad
\mylabel{AR-TApp} \quad
  \myirule{\tenv \vturns \forall \alpha. \rulet~\gbox{\leadsto E} \quad\quad \Gamma \turns \rulet'}
          {\tenv \vturns \rulet[\rulet'/\alpha]~\gbox{\leadsto E~||\rulet'||}}
\\ \\
\mylabel{AR-IAbs} \quad
  \myirule{\tenv, \rulet_1~\gbox{\leadsto x} \vturns \rulet_2~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
          {\tenv \vturns \rulet_1 \iarrow \rulet_2~\gbox{\leadsto
            \lambda\relation{x}{||\rulet_1||}.E}} 
\quad\quad\quad
\mylabel{AR-IApp} \quad
  \myirule{\tenv \vturns \rulet_1 \iarrow \rulet_2~\gbox{\leadsto E_2} \quad\quad \tenv \vturns \rulet_1~\gbox{\leadsto E_1}}
          {\tenv \vturns \rulet_2~~\gbox{\leadsto E_2~E_1}}
\ea
$
}
\end{center}
}

Figure~\ref{fig:resolution1} provides a first (ambiguous) definition of the
resolution judgement. Its underlying principle is
resolution in logic. 
Intuitively, $\tenv\vturns \rulet$ holds if $\tenv$ entails $\rulet$, where the types in $\tenv$ and
$\rulet$ are read as propositions.
Following the ``Propositions as Types'' correspondence~\cite{propsastypes}, we read
$\alpha$ as a propositional variable and $\forall \alpha.\rulet$ as universal quantification.
Yet, unlike in the traditional interpretation of types as propositions, we have two forms of arrow,
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
consider again the resolution in the last example of Section~\ref{sec:overview:ourlang}:
in the environment
\[
\Gamma_0 = (\tyint,\tybool,(\tybool\iarrow\tyint))
\]
there are two different derivations for
$\Gamma_0 \vturns \tyint$:
\begin{equation*}
\begin{array}{c}
\inferrule*[Left=\mylabel{AR-IVar}]
   {\tyint \in \Gamma_0}
   {\Gamma_0 \vturns \tyint}
\end{array}
\quad \text{and} \quad\quad\quad\quad\quad\quad
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

%-------------------------------------------------------------------------------
\subsection{Deterministic Resolution}\label{subsec:det}

% In order to eradicate the non-determinism in resolution we implement the following
% measures:
% \begin{enumerate}
% \item We provide a syntax-directed definition of resolution, based on the idea of
%       \emph{focused proof search} in logic~\cite{focusing,Miller91b,Liang:2009}, where at most one
%       rule applies in any given situation. 
% 
%       Our approach organizes resolution into two alternating phases that
%       pivots on an environment lookup (\mylabel{R-IVar}) which shifts
%       the focus from the queried type to an implicit rule type in the environment. 
%       The first phase performs \emph{backward chaining}: it applies only
%       elimination rules (\mylabel{R-TAbs},\mylabel{R-IAbs}) to the query type
%       to reason towards the given rules in the environment.
% 
%       In constrast, the second phase performs \emph{forward chaining}; it
%       reasons from the selected environment rule towards the query type. It does so
%       by applying only introduction rules (\mylabel{R-TApp},\mylabel{R-IApp}), but in
%       \emph{inverted form}, i.e., from the environment type towards the query type.
% 
% \item Our approach differs from focused proof search in the selection of the focus.
%       This is typically a nondeterminstic choice in focused proof search, but we make
%       it deterministic in two ways: 
%       \begin{enumerate}
%       \item by implementing a stack discipline: only the first (in LIFO order) matching rule type can be selected, and
%       \item we do not include any recursive resolutions in the matching decisions; this keeps
%             matching a shallow procedure which does not require any form of backtracking.
%       \end{enumerate}
% 
% \item We rule out two forms of non-determinism in the instantiation of
%       polymorphic types:
%       \begin{enumerate}
%       \item We disallow ambiguous types where quantified type variables
%             are not determined by the head of the type, such as 
%             $\forall \alpha.\tyint$ or $\forall \alpha. \alpha \iarrow \tyint$.
% 
%       \item We do not allow type variables to be instantiated by types with
%             abstractions (universal quantifiers or implicit arrows) as these
%             may subsequently be eliminated again (possibly by instantiation 
%             with other abstractions). For instance, $\forall \alpha. \alpha \iarrow \alpha$
% 	    can be instantiated directly with $[\tyint/\alpha]$ to $\tyint
% \iarrow \tyint$.  Alternatively, it could be first instantiated with $[(\forall
% \beta. \beta \iarrow \beta)/\alpha]$ to $(\forall \beta. \beta \iarrow \beta)
% \iarrow \forall \beta'. \beta' \iarrow \beta'$, and then after further
% instantiation of the outer context and of $\beta'$ with $[\tyint/\beta']$ also
% to $\tyint \iarrow \tyint$.
%  
%       \end{enumerate}
% 
% \end{enumerate}

Figure~\ref{fig:resolution2} defines judgement $\tenv \ivturns \rulet$, which
is a syntax-directed deterministic variant of $\tenv \vturns \rulet$. This
deterministic variant is sound with respect to the ambiguous definition. In
other words, $\tenv \vturns \rulet$ holds if $\tenv \ivturns \rulet$ holds.
Yet, the opposite is not true. The deterministic judgement sacrifices some
expressive power in exchange for better behavedness.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Revised Syntax}

To facilitate the definition of the deterministic resolution
judgement we split the syntax of types into three different
sorts: \emph{context} types, \emph{simple} types and \emph{monotypes}.
{\bda{llrl}
    \text{Context Types} & \rulet \hide{\in 2^\meta{RType}} & ::= & 
    \forall \alpha. \rulet \mid \rulet_1 \iarrow \rulet_2 \mid \type \\
    \text{Simple Types}  & \type                            & ::=  & \alpha \mid \rulet_1 \arrow \rulet_2 \\
    \text{Monotypes}     & \suty                            & ::=  & \alpha \mid \suty \arrow \suty
    % \text{Expressions} & |e| & ::=  &
    % x \mid \lambda (x:\rulet).e \mid e_1\,e_2 \mid \Lambda \alpha. e \mid e\,\rulet \mid \query \rulet \mid \ilambda \rulet. e \mid e_1 \with e_2 \\
  \eda }

 \emph{Context types} $\rulet$ correspond to the original types $\rulet$.
\emph{Simple types} $\type$ are a restricted form of context types without
toplevel quantifiers and toplevel implicit arrows. Singling out this restricted
form turns out to be convenient for the type-directed formulation of the judgement.

\emph{Monotypes} $\suty$ are a further refinement of simple types without
universal quantifiers and implicit arrows anywhere. They help us to address a
form of ambiguity due to the \emph{impredicativity} of Rule~\mylabel{AR-TApp}.
For instance, if we define $\tenv_1 = \forall \alpha.\alpha \iarrow \alpha$,
then there are two ways to resolve $\tenv_1 \vdash \tyint \iarrow \tyint$: 

%       \item We do not allow type variables to be instantiated by types with
%             abstractions (universal quantifiers or implicit arrows) as these
%             may subsequently be eliminated again (possibly by instantiation 
%             with other abstractions). For instance, $\forall \alpha. \alpha \iarrow \alpha$
% 	    can be instantiated directly with $[\tyint/\alpha]$ to $\tyint
% \iarrow \tyint$.  Alternatively, it could be first instantiated with $[(\forall
% \beta. \beta \iarrow \beta)/\alpha]$ to $(\forall \beta. \beta \iarrow \beta)
% \iarrow \forall \beta'. \beta' \iarrow \beta'$, and then after further
% instantiation of the outer context and of $\beta'$ with $[\tyint/\beta']$ also
% to $\tyint \iarrow \tyint$.
\begin{equation*}
\begin{array}{@@{\hspace{2cm}}c@@{\hspace{2cm}}c}
\inferrule*[Left=\mylabel{AR-TApp}]
  {\inferrule*[Left=\mylabel{AR-IVar}] 
    {(\forall \alpha.\alpha \iarrow \alpha) \in \tenv_1}
    {\tenv_1 \vturns \forall \alpha. \alpha \iarrow \alpha    }
  }
  {\tenv \vturns \tyint \iarrow \tyint}
&
\inferrule*[Left=\mylabel{AR-TApp}]
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
  {\tenv \vturns \tyint \iarrow \tyint}
\end{array}
\end{equation*}

The proof on the left only involves the predicative generalisation from
$\tyint$ to $\alpha$. Yet, the second proof contains an impredicative
generalisation from $\forall \beta. \beta \iarrow \beta$ to $\alpha$.
Impredicativity is a well-known source of such problems in other settings, such
as in type inference for the polymorphic $\lambda$-calculus~\cite{boehm85,pfenning93}. The established solution also works here: restrict to predicativity. This is where the monotype
sort $\suty$ comes in: we only allow generalisation over (or dually,
instantiation with) monotypes $\suty$.

% ------------------------------------ R-IVar
% forall a. a => a |- forall a. a => a
% ------------------------------------ R-TApp
% forall a. a => a |- int => int
% 
% 
% ------------------------------------ R-IVar
% forall a. a => a |- forall a. a => a
% ------------------------------------------------------------ R-TApp
% forall a. a => a |- (forall b. b => b) => (forall b. b => b)              ...
% ------------------------------------------------------------------------------------------
% forall a. a => a |- forall b. b => b
% ------------------------------------ R-TApp
% forall a. a => a |- int => int

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Revised Resolution Rules}

\newcommand{\elookup}[3][\bar{\alpha}]{{#2}_{#1}\langle{#3}\rangle}

\figtwocol{fig:resolution2}{Deterministic Resolution and Translation to System F}{
\begin{center}
\framebox{$
\ba{c}
\Sigma ::= \epsilon \mid \Sigma, \rulet~\gbox{\leadsto x} \\ \\
\myruleform{\tenv \ivturns \rulet~\gbox{\leadsto E}}
\quad\quad\quad 
\mylabel{R-Main} \quad
  \myirule{\mathit{tyvars}(\tenv);\tenv \ivturns \rulet~\gbox{\leadsto E}}
          {\tenv \ivturns \rulet~\gbox{\leadsto E}} \\ \\
\multicolumn{1}{c}{\myruleform{\bar{\alpha}; \tenv \ivturns \rulet~\gbox{\leadsto E}}} \\ \\
%%\quad\quad\quad
\mylabel{R-IAbs} \quad
  \myirule{\bar{\alpha};\tenv, \rulet_1~\gbox{\leadsto x} \ivturns \rulet_2~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
          {\bar{\alpha};\tenv \ivturns \rulet_1 \iarrow \rulet_2~\gbox{\leadsto
            \lambda\relation{x}{||\rulet_1||}.E}} 
\quad\quad
\mylabel{R-TAbs} \quad
  \myirule{\bar{\alpha};\tenv,\alpha \ivturns \rulet~\gbox{\leadsto E}}
          {\bar{\alpha};\tenv \ivturns \forall \alpha. \rulet~\gbox{\leadsto \Lambda\alpha.E}} 
\\ \\
\mylabel{R-Simp} \quad
 \myirule{\bar{\alpha};\tenv;\tenv \ivturns \type~\gbox{\leadsto E}}
         {\bar{\alpha};\tenv \ivturns \type~\gbox{\leadsto E}} 
\\ \\ \\
\myruleform{\bar{\alpha};\tenv;\tenv' \ivturns \type~\gbox{\leadsto E}}\\ \\

\mylabel{L-RuleMatch} \quad
  \myirule{\tenv; \rulet~\gbox{\leadsto x} \ivturns \tau~\gbox{\leadsto E}; \overline{\rulet~\gbox{\leadsto x}} \\
            \bar{\alpha};\tenv \ivturns \bar{\rulet}~\gbox{\leadsto \bar{E}}
          }
          {\bar{\alpha};\tenv;\tenv',\rulet~\gbox{\leadsto x} \ivturns \type~\gbox{\leadsto E[\bar{E}/\bar{x}]}} \quad\quad\quad
\mylabel{L-RuleNoMatch} \quad
  \myirule{
	\mathit{stable}(\bar{\alpha},\tenv,\rulet,\type) \\
%   \not\exists \theta, E, \Sigma, \mathit{dom}(\theta) \subseteq \bar{\alpha}: \theta(\tenv); \theta(\rulet)~\gbox{\leadsto x} \ivturns \theta(\tau)~\gbox{\leadsto E}; \Sigma \\
           \bar{\alpha};\tenv;\tenv' \ivturns \type~\gbox{\leadsto E'}
          }
          {\bar{\alpha};\tenv;\tenv',\rulet~\gbox{\leadsto x} \ivturns \type~\gbox{\leadsto E'}} \\ \\
\mylabel{L-Var} \quad
  \myirule{\bar{\alpha};\tenv;\tenv' \ivturns \type~\gbox{\leadsto E}
          }
          {\bar{\alpha};\tenv;\tenv',x:\rulet \ivturns \type~\gbox{\leadsto E}} 
\quad\quad\quad
\mylabel{L-TyVar} \quad
  \myirule{\bar{\alpha};\tenv;\tenv' \ivturns \type~\gbox{\leadsto E}
          }
          {\bar{\alpha};\tenv;\tenv',\alpha \ivturns \type~\gbox{\leadsto E}} 
\\ \\ \\
\myruleform{\tenv; \rulet~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma}\\ \\
\mylabel{M-Simp} \quad
          {\tenv; \type~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E}; \epsilon} \\ \\
\mylabel{M-IApp} \quad
  \myirule{\tenv, \rulet_1 \gbox{\leadsto x}; \rulet_2 ~\gbox{\leadsto E\,x} \ivturns \type~\gbox{\leadsto E'}; \Sigma 
           \quad\quad\quad \gbox{x~\mathit{fresh}}
          }
          {\tenv; \rulet_1 \iarrow \rulet_2 ~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma, \rulet_1~\gbox{\leadsto x}} \\ \\ 
\mylabel{M-TApp} \quad
  \myirule{\tenv; \rulet[\suty/\alpha] ~\gbox{\leadsto E\,||\suty||} \ivturns \type~\gbox{\leadsto E'}; \Sigma
           \quad\quad\quad
           \tenv \turns \suty
          }
          {\tenv; \forall \alpha. \rulet ~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma} \\ \\ \\
\myruleform{\mathit{stable}(\bar{\alpha},\tenv,\rulet,\type)}
\quad\quad\quad 
\mylabel{Stable} \quad
  \myirule{\not\exists \theta, E, \Sigma, \mathit{dom}(\theta) \subseteq \bar{\alpha}: \theta(\tenv); \theta(\rulet)~\gbox{\leadsto x} \ivturns \theta(\tau)~\gbox{\leadsto E}; \Sigma}
          {\mathit{stable}(\bar{\alpha},\tenv,\rulet,\type)}
\ea
$
}
\end{center}
}

Figure~\ref{fig:resolution2} defines the main judgement $\tenv \ivturns \rulet$ 
in terms of three interdependent auxiliary judgements. The first of these
auxiliary judgements is $\bar{\alpha};\tenv \ivturns \rulet$, where
the type variables $\bar{\alpha}$ are the free type variables in the
original environment at the point of the query. Recall the |bad| example
from Section~\ref{sec:overview:incoherence} where there is only one such free
type variable: |b|. 
Tracking these free variables plays a crucial role in guaranteeing coherence
and ensuring that resolution is stable under all type substitutions that instantiate these variables, like $[|b| \mapsto |Int|]$; how we prevent these substitutions is explained below.  The
main judgement
retains these free variables in rule \mylabel{R-Main} with 
the function $\mathit{tyvars}$:
\newcommand{\tyvars}[1]{\mathit{tyvars}(#1)}
\begin{equation*}
\begin{array}{rcl@@{\hspace{2cm}}rcl}
\tyvars{\epsilon}     & = & \epsilon &
\tyvars{\tenv,\alpha} & = & \tyvars{\tenv},\alpha \\
\tyvars{\tenv,x : \rulet} & = & \tyvars{\tenv} &
\tyvars{\tenv,\rulet~\gbox{\leadsto x}} & = & \tyvars{\tenv} 
\end{array}
\end{equation*}
While the auxiliary judgement $\bar{\alpha};\tenv \ivturns \rulet$ extends the
type environment $\tenv$, it does not update the type variables $\bar{\alpha}$.
This judgement is syntax-directed on the query type $\rulet$.  Its job is to
strip $\rulet$ down to a simple type $\type$ using literal copies of the
ambiguous rules \mylabel{AR-TAbs} and \mylabel{AR-IAbs}, and then to hand it
off to the second auxiliary judgement in rule \mylabel{R-Simp}.

The second auxiliary judgement, $\bar{\alpha}; \tenv; \tenv' \ivturns \type$,
is syntax-directed on $\tenv'$: it traverses $\tenv'$ from right to left until
it finds a rule type $\rulet$ that matches the simple type $\type$.  Rules
\mylabel{L-Var} and \mylabel{L-TyVar} skip the irrelevant entries in the
environment. Rule \mylabel{L-RuleMatch} identifies a matching rule type
$\rulet$ -- where matching is determined by with the third auxiliary judgement
-- and takes care of recursively resolving its context types; details follow
below.  Finally, rule \mylabel{L-RuleNoMatch} skips a rule type in the
environment if it does not match. Its condition
$\mathit{stable}(\bar{\alpha},\tenv,\rulet,\type)$ entails the opposite of rule
\mylabel{L-RuleMatch}'s first condition: $\not\exists
\Sigma:~\tenv;\rulet \ivturns \type; \Sigma$.
(We come back to the reason why the condition is stronger than this in
Section~\ref{sec:coherence}.)
As a consequence, rules \mylabel{L-RuleMatch} and \mylabel{L-RuleNoMatch}
are mutually excluse and \emph{the judgement effectively commits to the
right-most matching rule in $\tenv'$}.
We maintain the invariant that $\tenv'$ is a prefix of $\tenv$; rule
\mylabel{R-Simp} provides $\tenv$ as the initial value for $\tenv'$.
Hence, if a matching rule type $\rulet$ is found, we have that
$\rulet \in \tenv$. Hence, the second auxiliary judgement
plays much the same role as rule
\mylabel{AR-IVar} in Figure~\ref{fig:resolution1}, which also selects a rule type $\rulet \in \tenv$. The difference is that rule \mylabel{AR-IVar} makes a non-deterministic
choice, while the second auxiliary judgement makes deterministic committed choice
that prioritises rule types more to the right in the environment. For instance, $\tyint,\tyint \vturns \tyint$ has two ways to resolve, while $\tyint,\tyint \ivturns \tyint$ has only one because the second $\tyint$ in the environment shadows the first.


Finally, the third auxiliary judgement, $\tenv;\rulet \ivturns \type; \Sigma$,
determines whether the rule type $\rulet$ matches the simple type~$\type$. The
judgement is defined by structural induction on $\rulet$, which is step by step
instantiated to $\type$. 
Any recursive resolutions are deferred in this process -- the
postponed resolvents are captured in the $\Sigma$ argument. This
way they do not influence the matching decision and backtracking is avoided.
Instead, the recursive resolutions are executed, as part of rule
\mylabel{L-RuleMatch}, after the rule has been committed to.
Rule \mylabel{M-Simp} constitutes the base case where the rule type equals the
target type. Rule \mylabel{M-IApp} is the counterpart of the original
rule \mylabel{R-IApp} where the implication arrow $\rulet_1 \iarrow \rulet_2$
is instantiated to $\rulet_2$; the resolution of $\rulet_1$ is deferred.
Lastly, rule \mylabel{M-TApp} is the counterpart of the original rule \mylabel{R-TApp}.
The main difference is that it only uses
monotypes $\suty$ to substitute the type variable; this implements the predicativity
restriction explained above.

The relation to the ambiguous definition of resolution can be summarized as follows:
if $\tenv;\rulet \ivturns \type; \bar{\rulet}$
with
$\tenv \vturns \rulet$ and $\tenv \vturns \bar{\rulet}$, then
$\tenv \vturns \type$.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Non-Ambiguity Constraints}

The rule \mylabel{M-TApp} does not explain how the substitution
$[\suty/\alpha]$ for the rule type $\forall \alpha.\rulet$ should be obtained.
At first sight it seems that the choice of $\suty$ is free and thus a source of
non-determinism. However, in many cases the choice is not free at all, but is
instead determined fully by the simple type $\type$ that we want to match.
However, the choice is not always forced by the matching. Take for instance the context type $\forall \alpha. (\alpha \arrow \tystr)
\iarrow (\tystr \arrow \alpha) \iarrow (\tystr \arrow \tystr)$. This 
type encodes the well-known ambiguous Haskell type |forall a. (Show a, Read a) => String -> String| of the expression |read . show|. The
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
side-condition in rule \mylabel{Ty-IAbs} of Figure~\ref{fig:type}.\footnote{An
alternative design to avoid such ambiguity would instantiate unused type
variables to a dummy type, like GHC's \texttt{GHC.Prim.Any}, which is only used
for this purpose.} This judgement is defined in Figure~\ref{fig:unamb}
in terms of the auxiliary judgement $\bar{\alpha} \unamb \rulet$ which
takes an additional sequence of type variables $\alpha$ that is initially
empty.
\figtwocol{fig:unamb}{Unambiguous context types}{
\begin{center}
\framebox{
\begin{minipage}{\textwidth}
\bda{c}
\myruleform{\unamb \rulet} 
\quad\quad\quad
\mylabel{UA-Main} \quad
\myirule{\epsilon \unamb \rulet}
        {\unamb \rulet}
\\ \\
\myruleform{\bar{\alpha} \unamb \rulet} 
\quad\quad\quad
\mylabel{UA-Simp} \quad
\myirule{\bar{\alpha} \subseteq \mathit{ftv}(\type)}
        {\bar{\alpha} \unamb \type}
\\ \\
\mylabel{UA-TAbs} \quad
\myirule{\bar{\alpha},\alpha \unamb \rulet}
        {\bar{\alpha} \unamb \forall \alpha.\rulet} 
\quad\quad\quad
\mylabel{UA-IAbs} \quad
\myirule{\unamb \rulet_1 \quad\quad \bar{\alpha} \unamb \rulet_2}
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

Finally, the unambiguity condition is also imposed on the queried type $\rulet$
in rule \mylabel{Ty-Query} because this type too may extend the implicit
environment in rule \mylabel{R-IAbs}.

Note that the definition rules out harmless ambiguity, such as that in the type
$\forall \alpha. \tyint$. When we match the head of this type $\tyint$ with the
simple type $\tyint$, the matching succeeds without actually determining how
the type variable $\alpha$ should be instantiated. Here the ambiguity is
harmless, because it does not affect the semantics. Yet, for the sake of
simplicity, we have opted to not differentiate between harmless and harmful
ambiguity.

%-------------------------------------------------------------------------------
\paragraph{Coherence Enforcement}\label{sec:coherence}

In order to enforce coherence, rule \mylabel{L-RuleNoMatch} makes sure that the
decision to not select a context type is stable under all possible
substitutions $\theta$.  Consider for instance the |bad| example from Section~\ref{sec:overview:incoherence}: when looking up |b -> b|, the rule 
|Int -> Int| does not match and is otherwise skipped. Yet, under the substitution
$\theta = [|b| \mapsto |Int|]$ the rule would match after all. In
order to avoid this unstable situation, rule \mylabel{L-RuleNoMatch} only skips a context
type in the implicit environment, if there is no substitution $\theta$ for
which the type would match the context type.

This approach is similar to the treatment of overlapping type class instances
or overlapping type family instances in Haskell. However, there is one
important complicating factor here: the query type may contain universal
quantifiers.  Consider a query for |forall a. a -> a|. In this case we wish to
rule out entirely the context type |Int -> Int| as a potential match. Even
though it matches under the substitution $\theta = [|a| \mapsto |Int|]$,
that covers only one instantiation while the query clearly requires a resolvent that
covers all possible instantiations.

We clearly identify which type variables $\bar{\alpha}$ are to be considered
for substitution by rule \mylabel{L-RuleNoMatch} by parametrising the
judgements by this set. These are the type variables that occur in the environment
$\tenv$ at the point of the query. The main resolution judgement $\ivturns \rulet$
grabs them and passes them on to all uses of rule \mylabel{L-RuleNoMatch}.

%-------------------------------------------------------------------------------
\subsection{Algorithm}

\newcommand{\alg}{\turns_{\mathit{alg}}}
\newcommand{\coh}{\turns_{\mathit{coh}}}
\newcommand{\mgu}[3][\bar{\alpha}]{\textit{mgu}_{#1}(#2,#3)}
\newcommand{\mgun}[4][\tenv]{\textit{mgu}_{#1;#2}(#3,#4)}

Figure~\ref{fig:algorithm} contains an algorithm that implements the
non-algorithmic deterministic resolution rules of Figure~\ref{fig:resolution2}.
It differs from the latter in two important ways: 
firstly, it replaces explicit quantification over all substitutions $\theta$ in rule
\mylabel{L-RuleNoMatch} with a tractable approach to coherence checking;
and, secondly, it computes rather than guesses type substitutions in rule
\mylabel{M-TApp}. 

The definition of the algorithm is structured in much the same way
as the declarative specification: with one main judgement and three
auxiliary ones that have similar roles. In fact, since the differences
are not situated in the main and first auxiliary judgement, these are
actually identical.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Algorithmic No-Match Check}

The first difference is situated in rule \mylabel{Alg-L-RuleNoMatch} of the second
judgement. Instead of an explicit quantification over all possible
substitutions, this rule uses the more algorithmic judgement
$\bar{\alpha};\tenv;\rulet\coh\type$. This auxiliary judgement checks algorithmically
whether there context type $\rulet$ matches $\type$ under any possible instantiation
of the type variables $\bar{\alpha}$.
% \bda{c}
% \myruleform{\bar{\alpha};\rulet\coh \tau}
% \quad\quad\quad
% \mylabel{COH-Simp}\quad
% \myirule{\theta = \textit{mgu}_{\bar{\alpha}}(\tau,\tau')
%         }
%         {\bar{\alpha};\tau'\coh \tau}  \\ \\
% \mylabel{Coh-TApp}\quad
% \myirule{\bar{\alpha},\alpha;\rulet \coh \tau}
%         {\bar{\alpha};\forall \alpha. \rulet\coh \tau}  
% \quad\quad\quad
% \mylabel{Coh-IApp}\quad
% \myirule{\bar{\alpha};\rulet_2 \coh \tau}
%         {\bar{\alpha};\rulet_1 \iarrow \rulet_2\coh \tau}
% \eda

The definition of $\bar{\alpha};\tenv;\rulet \coh \type$ is a variation on that of
the declarative judgement $\tenv; \rulet \ivturns \type; \Sigma$. There are
three differences. 
% \begin{enumerate}
% \item
Firstly, since the judgement is only concerned with matchability, no recursive
resolvents $\Sigma$ are collected. 
% \item
Secondly, instead of guessing the type instantiation ahead of time in rule
$\mylabel{M-TApp}$, rule $\mylabel{Coh-TApp}$ defers the instantiation to the
base case, rule \mylabel{Coh-Simp}. This last rule performs the deferred
instantiation of type variables $\bar{\alpha}$ by computing the \emph{most general
domain-restricted unifier} $\theta = \mgun{\bar{\alpha}}{\type'}{\type}$.
A substitution $\theta$ is a unifier of two types $\rulet_1$ and $\rulet_2$ iff
$\theta(\rulet_1) = \theta(\rulet_2)$. A unifier $\theta$ is restricted to domain
$\bar{\alpha}$ if $\dom(\theta) \subseteq \bar{\alpha}$.
A most general domain-restricted unifier $\theta$ subsumes
any other unifier restricted to the same domain $\bar{\alpha}$:
\begin{equation*}
\forall \eta: \quad \mathit{dom}(\eta) \subseteq \bar{\alpha} \wedge
\eta(\rulet_1) = \eta(\rulet_2)  
\quad\Rightarrow\quad
\exists \iota: \mathit{dom}(\iota) \subseteq \bar{\alpha} \wedge
\iota(\theta(\rulet_1)) = \iota(\theta(\rulet_2))
\end{equation*}
If this most-general unifier exists, a match has been established.
If no unifier exists, then rule \textsc{COH-Simp} does not apply.
% \item
Thirdly, since the coherence check considers the substitution of the type variables
$\bar{\alpha}$ that occur in the environment at the point of the query, rule
\mylabel{Alg-L-RuleNoMatch} pre-populates the substitutable variables of the
$\coh$ judgement with them.
% \end{enumerate}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Deferred Variable Instantiation}
The second main difference is situated in the third auxiliary judgement
$\bar{\alpha};\tenv;\rulet;\Sigma \alg \type ; \Sigma'$. This judgement is 
in fact an extended version of $\bar{\alpha};\tenv;\rulet\coh\type$ that does 
collect the recursive resolution obligations in $\Sigma'$ just like the 
corresponding judgement in the declarative specification. The main difference
with the latter is that it uses the deferred approach to instantiating 
type variables. In order to subject the resolution obligations to this
substitution, which is computed in rule \mylabel{Alg-M-Simp}, the judgement
makes use of an accumulating parameter $\Sigma$.  This accumulator $\Sigma$
represents all the obligations collected so far in which type variables
have not been substituted yet. In contrast, $\Sigma'$ denotes all obligations
with type variables already substituted.
Finally, note that rule \mylabel{Alg-L-RuleMatch} does not pre-populate the 
type variables with those of the environment: we only want to instantiate
the type variables that appear in the context type $\rulet$ itself for an 
actual match.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Domain-Restricted Unification}

The algorithm for computing the most general domain-restricted unifier $\theta=
\mgun{\bar{\alpha}}{\rulet_1}{\rulet_2}$ is a key component of the two
algorithmic changes explained above.  Figure~\ref{fig:mgu} provides its
definition, which is an extension of standard first-order
unification~\cite{martellimonatanari}.  The domain restriction $\bar{\alpha}$
denotes which type variables are to be treated as unification variables; all
other type variables are to be treated as constants.  The differences with
standard first-order unification arise because the algorithm has to account for
type variable binders and the scope of type variables. For
instance, using standard first-order unification for $\mgun{\beta}{\forall
\alpha. \alpha \to \beta}{\forall \alpha.\alpha \to \alpha}$ would yield 
the substitution $[\beta/\alpha]$. However, this solution is not
acceptable because $\alpha$ is not in scope in $\tenv$.

Rule \mylabel{U-InstL} implements the base case for scope-safe unification.
It only creates a substitution $[\suty/\alpha]$ if $\alpha$ is one of the
unification variables and if its instantiation does not refer to any type variables
that have been introduced in the environment after $\alpha$. The latter
relation is captured in the auxiliary judgement $\beta >_\tenv \alpha$.
(We make an exception for unifiable type variables that have been introduced later:
while the most general unifier itself may not yield a valid instantiation, it still 
signifies the existence of an infinite number of more specific valid instantiations.)
Rule \mylabel{U-InstR} is the symmetric form of \mylabel{U-InstR}.

Rule \mylabel{U-Var} is the standard reflexivity rule. Rules \mylabel{U-Fun}
and \mylabel{U-Rul} are standard congruence rules that combine the
unifications derived for their subterms. Rule \mylabel{U-Univ} is a congruence
rule too, but additionally extends the environment $\tenv$ in the recursive
call with the new type variable $\beta$ that is in scope in the subterms.

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
\framebox{$
\ba{c}
\myruleform{\tenv \alg \rulet~\gbox{\leadsto E}} \quad\quad\quad

\mylabel{Alg-R-Main}\quad
\myirule{\mathit{tyvars}(\tenv);\tenv \alg \rulet~\gbox{\leadsto E}}
        {\tenv \alg \rulet~\gbox{\leadsto E}}  \\ \\

\myruleform{\bar{\alpha};\tenv \alg \rulet~\gbox{\leadsto E}} 

\quad\quad\quad

\mylabel{Alg-R-Simp}\quad
\myirule{\bar{\alpha};\tenv;\tenv \alg \tau~\gbox{\leadsto E}}
        {\bar{\alpha};\tenv \alg \tau ~\gbox{\leadsto E} }  \\ \\

\mylabel{Alg-R-IAbs}\quad
\myirule{\bar{\alpha};\tenv, \rulet_1~\gbox{\leadsto x} \alg \rulet_2~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
        {\bar{\alpha};\tenv \alg \rulet_1 \iarrow \rulet_2 ~\gbox{\leadsto \lambda(x : ||\rulet_1||). E}} \quad\quad\quad

\mylabel{Alg-R-TAbs}\quad
\myirule{\bar{\alpha};\tenv,\alpha \alg \rulet ~\gbox{\leadsto E}}
        {\bar{\alpha};\tenv \alg \forall \alpha. \rulet ~\gbox{\leadsto \Lambda \alpha. E}}  \\ \\

% \mylabel{Alg-Simp}\quad
% \myirule{\bar{\alpha};\tenv \turns_{\mathit{match1st}} \tau \hookrightarrow \bar{\rulet}\gbox{; \bar{\omega}; E} \quad\quad \bar{\alpha};\tenv \alg \rulet_i~\gbox{\leadsto E_i} \quad (\forall \rulet_i \in \bar{\rulet})}
%         {\bar{\alpha};\tenv \alg \tau ~\gbox{\leadsto E[\bar{\omega}/\bar{E}]} }  \\ \\

\multicolumn{1}{c}{\myruleform{\bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E} }} \\ \\

\mylabel{Alg-L-RuleMatch}\quad
\myirule{\epsilon; \tenv; \rulet~\gbox{\leadsto x}; \epsilon \alg \type~\gbox{\leadsto E}; \bar{\rulet}~\gbox{\leadsto \bar{x}} \quad\quad
         \bar{\alpha};\tenv \alg \bar{\rulet}~\gbox{\leadsto \bar{E}}}
        {\bar{\alpha};\tenv; \tenv', \rulet~\gbox{\leadsto x} \alg \type~\gbox{\leadsto E[\bar{E}/\bar{x}] }}  \\ \\

\mylabel{Alg-L-RuleNoMatch}\quad
\myirule{\bar{\alpha};\tenv;\rulet \not\coh \type \quad\quad
         \bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E'}}
        {\bar{\alpha};\tenv;\tenv', \rulet~\gbox{\leadsto x}\alg \type~\gbox{\leadsto E'}}  \\ \\
\mylabel{Alg-L-Var} \quad
  \myirule{\bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E}
          }
          {\bar{\alpha};\tenv;\tenv',x:\rulet \alg \type~\gbox{\leadsto E}} 
\quad\quad\quad
\mylabel{Alg-L-TyVar} \quad
  \myirule{\bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E}
          }
          {\bar{\alpha};\tenv;\tenv',\alpha \alg \type~\gbox{\leadsto E}} 
\\ \\

\multicolumn{1}{c}{\myruleform{\bar{\alpha}; \tenv; \rulet~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}} \\ \\

\mylabel{Alg-M-Simp}\quad
\myirule{\theta = \mgun{\bar{\alpha}}{\type}{\type'}
        }
        {\bar{\alpha}; \tenv; \type'~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto ||\theta||(E)}; \theta(\Sigma)}  \\ \\

\mylabel{Alg-M-IApp}\quad
\myirule{\bar{\alpha}; \tenv, \rulet_1~\gbox{\leadsto x}; \rulet_2~\gbox{\leadsto E\,x}; \rulet_1~\gbox{\leadsto x}, \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'\quad\quad \gbox{x~\mathit{fresh}}}
        {\bar{\alpha}; \tenv; \rulet_1 \iarrow \rulet_2~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}  \\ \\

\mylabel{Alg-M-TApp}\quad
\myirule{\bar{\alpha},\alpha; \tenv,\alpha; \rulet~\gbox{\leadsto E\,\alpha}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}
        {\bar{\alpha}; \tenv; \forall \alpha. \rulet~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'} 
\\ \\
\myruleform{\bar{\alpha};\tenv;\rulet\coh \tau}
\quad\quad\quad
\mylabel{COH-Simp}\quad
\myirule{\theta = \mgun{\bar{\alpha}}{\tau}{\tau'}
        }
        {\bar{\alpha};\tenv;\tau'\coh \tau}  \\ \\
\mylabel{Coh-TApp}\quad
\myirule{\bar{\alpha},\alpha;\tenv,\alpha;\rulet \coh \tau}
        {\bar{\alpha};\tenv;\forall \alpha. \rulet\coh \tau}  
\quad\quad\quad
\mylabel{Coh-IApp}\quad
\myirule{\bar{\alpha};\tenv;\rulet_2 \coh \tau}
        {\bar{\alpha};\tenv;\rulet_1 \iarrow \rulet_2\coh \tau}
\ea
$
}
\end{center}
}

\figtwocol{fig:mgu}{Most General Unifier}{
\begin{center}
\framebox{$
\ba{c}
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

\myruleform{\theta = \mgun{\bar{\alpha}}{\rulet_1}{\rulet_2}}
\hspace{1cm}

\mylabel{U-InstL}\quad\myirule{ 
	  \alpha \in \bar{\alpha}
          \quad\quad
          \forall \beta\in\mathit{ftv}(\suty):~~ \beta \in \bar{\alpha} \vee \beta >_\tenv \alpha
        } 
        { [\suty/\alpha] = \mgun{\bar{\alpha}}{\alpha}{\suty}}  \\ \\

\mylabel{U-Var}\quad
\myirule{
        } 
        { \epsilon = \mgun{\bar{\alpha}}{\beta}{\beta}}  \hspace{1cm}

\mylabel{U-InstR}\quad\myirule{ 
	  \alpha \in \bar{\alpha}
          \quad\quad
          \forall \beta\in\mathit{ftv}(\suty):~~ \beta \in \bar{\alpha} \vee \beta >_\tenv \alpha
        } 
        { [\suty/\alpha] = \mgun{\bar{\alpha}}{\suty}{\alpha}} \\ \\

\mylabel{U-Fun}\quad
\myirule{\theta_1 = \mgun{\bar{\alpha}}{\rulet_{1,1}}{\rulet_{2,1}}
         \quad\quad
         \theta_2 = \mgun{\bar{\alpha}}{\theta_1(\rulet_{1,2})}{\theta_1(\rulet_{2,2})}
        } 
        {\theta_2 \cdot \theta_1 = \mgun{\bar{\alpha}}{\rulet_{1,1} \arrow \rulet_{1,2}}{\rulet_{2,1} \arrow \rulet_{2,2}}}  \\ \\


\mylabel{U-Rul}\quad
\myirule{\theta_1 = \mgun{\bar{\alpha}}{\rulet_{1,1}}{\rulet_{2,1}}
         \quad\quad
         \theta_2 = \mgun{\bar{\alpha}}{\theta_1(\rulet_{1,2})}{\theta_1(\rulet_{2,2})}
        } 
        {\theta_2 \cdot \theta_1 = \mgun{\bar{\alpha}}{\rulet_{1,1} \iarrow \rulet_{1,2}}{\rulet_{2,1} \iarrow \rulet_{2,2}}}  \\ \\

\mylabel{U-Univ}\quad
\myirule{\theta = \mgun[\tenv,\beta]{\bar{\alpha}}{\rulet_{1}}{\rulet_{2}}
        } 
        {\theta = \mgun{\bar{\alpha}}{\forall \beta.\rulet_{1}}{\forall \beta.\rulet_{2}}}  \\ \\

\myruleform{\beta >_\tenv \alpha}
\hspace{1cm}
\myirule{
}
{ \beta >_{\tenv_1,\beta,\tenv_2,\alpha,\tenv_3} \alpha }

\ea
$
}
\end{center}
}

%===============================================================================

%-------------------------------------------------------------------------------
\subsection{Termination of Resolution}

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

\newcommand{\term}[1]{\turns_\mathit{term} #1}
\newcommand{\occ}[2]{\mathit{occ}_{#1}(#2)}
\newcommand{\tnorm}[1]{\||#1\||}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Termination Condition}
The problem of non-termination has been widely studied in the context of
Haskell's type classes, and a set of modular syntactic restrictions
has been imposed on type class instances to avoid non-termination~\cite{fdchr}. 
Adapting these restrictions to our setting, we obtain the termination
judgement $\term{\rulet}$ defined in Figure~\ref{fig:termination}.

This judgement recursively constrains rule types $\rulet_1 \iarrow \rulet_2$ to
guarantee that the recursive resolution process is well-founded. In particular,
it defines a size measure $\||\rulet\||$ for type terms $\rulet$ and makes sure that the size 
of the resolved head type decreases steadily with each recursive resolution
step. 

The size measure does not take 
universally quantified type variables into account. It assigns them size 1 but
ignores the fact that the size may increase dramatically when the type variable
is instantiated with a large type. The rule $\TermRule$ makes up for this 
by requiring a size decrease for all possible instantiations of free type variables.
However, rather than to specify this property non-constructively as 
\[ \forall \bar{\rulet}: \quad \||[\bar{\alpha}\mapsto\bar{\rulet}]\tau_1\|| < \||[\bar{\alpha}\mapsto\bar{\rulet}]\tau_2\|| \]
it provides a more practical means to verify this condition by way of free variable occurrences.
The number of occurrences $\occ{\alpha}{\tau_1}$ of free variable $\alpha$ in type $\tau_1$ should be less than the number
of occurrences 
$\occ{\alpha}{\tau_2}$ in $\tau_2$. It is easy to see that the non-constructive property follows from this requirement.

\paragraph{Integration in the Type System}
There are various ways to integrate the termination condition in the type system. 
The most generic approach is to require that all types satisfy the termination condition.
This can be done by making the condition part of the well-formedness relation for types.

\figtwocol{fig:termination}{Termination Condition}{
\begin{center}
\framebox{
\begin{minipage}{.81\textwidth}
\begin{equation*}
\ba{c}
\myruleform{\term{\rulet}}
\quad\quad\quad
\TermSimpl \quad
  \myirule{}
          {\term{\tau}} 
\quad\quad\quad
\TermForall \quad
  \myirule{\term{\rulet}}
          {\term{\forall \alpha. \rulet}} 
\\ \\
\TermRule \quad
  \myirule{\term{\rulet_1} \quad\quad \term{\rulet_2} \\ 
           \tau_1 = \head{\rulet_1} \quad\quad \tau_2 = \head{\rulet_2} \quad\quad \tnorm{\tau_1} < \tnorm{\tau_2} \\
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
      \tnorm{\alpha} & = & 1 &
      \tnorm{\forall \alpha.\rulet} & = & \tnorm{\rulet} \\
      \tnorm{\rulet_1 \arrow \rulet_2} & = & 1 + \tnorm{\rulet_1} + \tnorm{\rulet_2} &
      \tnorm{\rulet_1 \iarrow \rulet_2} & = & 1 + \tnorm{\rulet_1} + \tnorm{\rulet_2} 
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

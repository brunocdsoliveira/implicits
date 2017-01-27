%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Rule.fmt

\newcommand{\rhs}[1]{\mathit{rhs}(#1)}
\newcommand{\lhs}[1]{\mathit{lhs}(#1)}
\newcommand{\qtv}[1]{\mathit{qtv}(#1)}
\newcommand{\ftv}[1]{\mathit{ftv}(#1)}

\section{The $\ourlang$ Calculus}
\label{sec:ourlang}

This section formalizes the syntax and type system of $\ourlang$.  In
Section~\ref{sec:trans} (building on top of this type system) we present the
formalization of the type-directed translation to System F. However, to avoid
duplication and to facilitate readability, we present the rules of the type
system and type-directed translation together. We use grey boxes to indicate
the parts of the rules that belong to the type-directed translation. These
greyed parts are explained in Section~\ref{sec:trans} and can be ignored in the
remainder of this section.

%-------------------------------------------------------------------------------
\subsection{Syntax}    
\label{subsec:syntax}

This is the syntax of the calculus:
{\bda{llrl}
    \text{Types} & \rulet  & ::=  & \alpha \mid \rulet_1 \arrow \rulet_2 \mid \forall \alpha. \rulet \mid \rulet_1 \iarrow \rulet_2 \\
    \text{Expressions} & |e| & ::=  &
     x \mid \lambda (x:\rulet).e \mid e_1\,e_2 \mid \Lambda \alpha. e \mid e\,\rulet \mid \query \rulet \mid \ilambda \rulet. e \mid e_1 \with e_2  \\
  \eda }

\textit{Types} $\rulet$ comprise four constructs: type variables
$\alpha$; function types $\rulet_1 \arrow \rulet_2$; type abstraction
$\forall \alpha. \rulet$; and the novel \emph{rule type} $\rulet_1 \iarrow
\rulet_2$.  In a rule type $\rulet_1 \iarrow \rulet_2$, type $\rulet_1$ is
called the \textit{context} and type $\rulet_2$ the \textit{head}.

Expressions $e$ include three
abstraction-eliminination pairs. The
binder $\lambda (x:\rulet). e$ abstracts expression $e$ over values of type $\rulet$, is eliminated by
application $e_1\,e_2$ and refers to the bound value with variable $x$.
The binder $\Lambda \alpha.e$ abstracts expression $e$ over types, is eliminated
by type application $e\,\rulet$ and refers to the bound type with type variable $\alpha$ 
(but $\alpha$ itself is not a valid expression). The binder $\ilambda \rulet. e$ 
abstracts expression $e$ over implicit values of type $\rulet$, is eliminated by
implicit application $e_1 \with e_2$ and refers to the implicitly bound value with 
implicit query $\query \rulet$.
Without loss of generality we assume that all variables $x$
and type variables $\alpha$ in binders are distinct. If not, they
can be easily renamed apart to be so.

Using rule abstractions and applications we can build the |implicit| 
sugar that we have used in Sections~\ref{sec:intro} and \ref{sec:overview}.
%{
%format == = "\defeq"
%format e1

\[ | implicit {-"\overline{"-} e : {-"\rulet}"-} in e1 == ({-" \overline{\lambda_? \rulet .} "-} e1) {-"\overline{"-} with e {-"}"-} | \]
%}\bruno{Also introduce let, which is used later, in the translation.}

The notation $\overline{\lambda_? \rulet .}$ is a short form for 
$\lambda_? \rulet_1.~\ldots~\lambda_? \rulet_n.$. Correspondingly,
the notation $\overline{|with|~e}$ is a short form for
|with| $e_1 \ldots $ |with| $e_n$.

For brevity we have kept the $\ourlang$ calculus small. Examples
may use additional syntax such as built-in integers, integer operators and boolean
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
              \quad\quad\quad
              \alpha \not\in \tenv \quad\quad\quad 
           }
           { \tenv \turns \relation{\Lambda \alpha.e}{\forall
               \alpha.\rulet}~\gbox{\leadsto \Lambda \alpha.E_1} } \quad\quad\quad
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
             \quad \epsilon \vdash_{\mathit{unamb}} \rulet_1
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
{ \tenv \vturns \rulet~\gbox{\leadsto E} \quad\quad\quad \tenv \turns \rulet \quad\quad\quad \epsilon \vdash_{\mathit{unamb}} \rulet}
{ \tenv \turns \relation{?\rulet}{\rulet}~\gbox{\leadsto E}
} 
\eda
\bda{c}
\myruleform{\bar{\alpha} \vdash_{\mathit{unamb}} \rulet} \\ \\
\mylabel{UA-TAbs} \quad
\myirule{\bar{\alpha},\alpha \vdash_{\mathit{unamb}} \rulet}
        {\bar{\alpha} \vdash_{\mathit{unamb}} \forall \alpha.\rulet} 
\quad\quad\quad
\mylabel{UA-IAbs} \quad
\myirule{\epsilon \vdash_{\mathit{unamb}} \rulet_1 \quad\quad \bar{\alpha} \vdash_{\mathit{unamb}} \rulet_2}
        {\bar{\alpha} \vdash_{\mathit{unamb}} \rulet_1 \iarrow \rulet_2} \\ \\
% \mylabel{UA-TAbsAlt} \quad
% \myirule{\bar{\alpha} \vdash_{\mathit{unamb}} \rulet}
%         {\bar{\alpha} \vdash_{\mathit{unamb}} \forall \alpha.\rulet}
% \quad\quad\quad
% \mylabel{UA-IAbsAlt} \quad
% \myirule{\epsilon \vdash_{\mathit{unamb}} \rulet_1 \quad\quad \bar{\alpha},\mathit{ftv}(\rulet_1) \vdash_{\mathit{unamb}} \rulet_2}
%         {\bar{\alpha} \vdash_{\mathit{unamb}} \rulet_1 \iarrow \rulet_2} \\ \\
\mylabel{UA-Simp} \quad
\myirule{\bar{\alpha} \subseteq \mathit{ftv}(\type)}
        {\bar{\alpha} \vdash_{\mathit{unamb}} \type}
\quad\quad\quad
\text{TODO: postpone until $\type$ is introduced}
\eda
\end{minipage}
}
\end{center}
}
\bruno{Another point I remember discussing with Philip is whether the unambiguity check can be combined with termination
checking. Should we consider this option?}

Figure \ref{fig:type} presents the static type system of $\ourlang$. The type system 
is based on the type system of System F, and every System F term is typeable in our 
system.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Well-Formed Types}

The judgement $\tenv \turns \rulet$ denotes
the well-formedness of types with respect to type environment $\tenv$. As
in System F, the type environment $\tenv$ records the type variables $\alpha$
and the variables $x$ with associated type $\rulet$ in scope. New here is that
it also records the types of the implicit rules $\rulet$:
\bda{llrl} 
\text{Type Environments}     & \tenv & ::= & \epsilon \mid \tenv, \relation{x}{\rulet} \mid \tenv , \alpha \mid \tenv, \rulet~\gbox{\leadsto x} \\
\eda
Types $\rulet$ are well-formed iff their free type variables occur in the type
environment $\WFVarTy$.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Well-Typed Expressions}

The typing judgment ${\tenv \turns \relation{e}{\rulet}}$ means that
expression $e$ has type $\rulet$ with respect to type environment $\tenv$.
Most of the rules are literal copies of the corresponding System F typing rules; only three deserve special attention.
Firstly, rule \TyIAbs{} extends the implicit environment with the type of an implicit value. 
The side condition $\epsilon \vdash_{\mathit{unamb}} \rulet$ states that
the type $\rulet_1$ must be unambiguous; we explain this concept in Section~\ref{subsec:det}.
Secondly, rule \TyIApp{} eliminates an implicit abstraction by supplying a 
value of the required type. Finally, rule \TyQuery{} resolves 
a particular unambiguous type $\rulet$ against the implicit environment.
It is defined in terms of the auxiliary judgement $\tenv \vturns \rulet$, which
is explained next.

%-------------------------------------------------------------------------------
\subsection{Resolution}\label{s:resolution}

\figtwocol{fig:resolution1}{Ambiguous Resolution}{
\begin{center}
\framebox{$
\ba{c}
\multicolumn{1}{c}{\myruleform{\tenv \vturns \rulet~\gbox{\leadsto E}}} \\ \\

\mylabel{R-TAbs} \quad
  \myirule{\tenv, \alpha \vturns \rulet~\gbox{\leadsto E}}
          {\tenv \vturns \forall \alpha. \rulet~\gbox{\leadsto \Lambda\alpha.E}} 
\quad\quad\quad
\mylabel{R-TApp} \quad
  \myirule{\tenv \vturns \forall \alpha. \rulet~\gbox{\leadsto E} \quad\quad \Gamma \turns \suty}
          {\tenv \vturns \rulet[\suty/\alpha]~\gbox{\leadsto E~||\suty||}}
\\ \\
\mylabel{R-IVar} \quad
  \myirule{\rulet~\gbox{\leadsto x} \in \tenv}
          {\tenv \vturns \rulet~\gbox{\leadsto x}}
\quad\quad\quad
\mylabel{R-IAbs} \quad
  \myirule{\tenv, \rulet_1~\gbox{\leadsto x} \vturns \rulet_2~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
          {\tenv \vturns \rulet_1 \iarrow \rulet_2~\gbox{\leadsto
            \lambda\relation{x}{||\rulet_1||}.E}} 
\\ \\
\mylabel{R-IApp} \quad
  \myirule{\tenv \vturns \rulet_1 \iarrow \rulet_2~\gbox{\leadsto E_2} \quad\quad \tenv \vturns \rulet_1~\gbox{\leadsto E_1}}
          {\tenv \vturns \rulet_2~~\gbox{\leadsto E_2~E_1}}
\\ \\

\ea
$
}
\end{center}
}

The underlying principle of resolution in $\ourlang$ originates
from resolution in logic. 
Intuitively, $\tenv\vdash_r \rulet$ holds if $\tenv$ entails $\rulet$, where the types in $\tenv$ and
$\rulet$ are read as propositions.
Following the Curry-Howard correspondence, we read
$\alpha$ as a propositional variable, $\forall \alpha.\rulet$ as universal quantification, and
rule types $\rulet_1 \iarrow \rulet_2$ as implication. We do not give a special interpretation to
the function type $\rulet_1 \arrow \rulet_2$, treating it as an uninterpreted predicate.
Unlike traditional Curry-Howard, we have two forms of arrow, functions and rules,
and the important twist on the traditional correspondence is that we choose to treat
rules as implications, leaving functions as uninterpreted predicates.

Figure~\ref{fig:resolution1} provides a first (ambiguous) definition of the
resolution judgement $\env \vturns \rulet$ that corresponds to the intuition of
logical implication checking. However, it suffers from two problems: 
\begin{enumerate}
\item 
The definition is \emph{not syntax-directed}; several of the inference rules have
overlapping conclusions. Hence, a deterministic resolution algorithm is
non-obvious.
\item
More importantly, the definition is \emph{ambiguous}: a derivation can be shown by
multiple different derivations. For instance, there are two different derivations
for
$\tyint,\tybool,\tybool\iarrow\tyint \vturns \tyint$:
\begin{equation*}
\begin{array}{c}
\inferrule*[Left=\mylabel{R-IVar}]
   {\tyint \in (\tyint,\tybool,\tybool\iarrow\tyint)
   }
   {\tyint,\tybool,\tybool\iarrow\tyint \vturns \tyint}
\end{array}
\end{equation*}
\noindent and
\begin{equation*}
\begin{array}{c}
\inferrule*[Left=\mylabel{R-IApp}]
   {\inferrule*[Left=\mylabel{R-IVar}] {(\tybool \iarrow \tyint) \in (\tyint,\tybool,\tybool\iarrow\tyint)}
                {\tyint,\tybool,\tybool\iarrow\tyint \vturns (\tybool \iarrow \tyint)} \\
    \inferrule*[left=\mylabel{R-IVar}] {\tybool \in (\tyint,\tybool,\tybool\iarrow\tyint)}
                {\tyint,\tybool,\tybool\iarrow\tyint \vturns \tybool}
   }
   {\tyint,\tybool,\tybool\iarrow\tyint \vturns \tyint}
\end{array}
\end{equation*}
While this may seem harmless at the type-level, at the value-level each
derivation corresponds to a (possibly) different value. Hence, ambiguous
resolution renders the meaning of a program ambiguous.
\end{enumerate}

%-------------------------------------------------------------------------------
\subsection{Deterministic Resolution}\label{subsec:det}

In order to eradicate the non-determinism in resolution we implement the following
measures:
\begin{enumerate}
\item We provide a syntax-directed definition of resolution, based on the idea of
      \emph{focused proof search} in logic~\cite{}, where at most one
      rule applies in any given situation. 

      This approach organizes resolution into two alternating phases that
      pivots on an environment lookup (\mylabel{R-IVar}) which shifts
      the focus from the queried type to an implicit rule type in the environment: 
      the first phase only allows only elimination rules
      (\mylabel{R-TAbs},\mylabel{R-IAbs}), and the second phase only introduction
      rules (\mylabel{R-TApp},\mylabel{R-IApp}) which are applied in inverted
      form on the focused rule type rather than the query type.

\item Our approach differs from focused proof search in the selection of the focus.
      This is typically a nondeterminstic choice in focused proof search, but we make
      it deterministic in two ways: 
      \begin{enumerate}
      \item by implementing a stack discipline: only the first (in LIFO order) matching rule type can be selected, and
      \item we do not include any recursive resolutions in the matching decisions; this keeps
            matching a shallow procedure which does not require any form of backtracking.
      \end{enumerate}

\item We rule out two forms of non-determinism in the instantiation of
      polymorphic types:
      \begin{enumerate}
      \item We disallow ambiguous types where quantified type variables
            are not determined by the head of the type, such as 
            $\forall \alpha.\tyint$ or $\forall \alpha. \alpha \iarrow \tyint$.

      \item We do not allow type variables to be instantiated by types with
            abstractions (universal quantifiers or implicit arrows) as these
            may subsequently be eliminated again (possibly by instantiation 
            with other abstractions). For instance, $\forall \alpha. \alpha \iarrow \alpha$
	    can be instantiated directly with $[\tyint/\alpha]$ to $\tyint
\iarrow \tyint$.  Alternatively, it could be first instantiated with $[(\forall
\beta. \beta \iarrow \beta)/\alpha]$ to $(\forall \beta. \beta \iarrow \beta)
\iarrow \forall \beta'. \beta' \iarrow \beta'$, and then after further
instantiation of the outer context and of $\beta'$ with $[\tyint/\beta']$ also
to $\tyint \iarrow \tyint$.
 
      \end{enumerate}

\end{enumerate}


%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Revised Syntax}

To implement measures (1) and (3b), we provide a variant of the syntax of the
calculus:

{\bda{llrl}
    \text{Context Types} & \rulet \hide{\in 2^\meta{RType}} & ::= & 
    \forall \alpha. \rulet \mid \rulet_1 \iarrow \rulet_2 \mid \type \\
    \text{Simple Types}  & \type                            & ::=  & \alpha \mid \rulet_1 \arrow \rulet_2 \\
    \text{Monotypes}     & \suty                            & ::=  & \alpha \mid \suty \arrow \suty
    % \text{Expressions} & |e| & ::=  &
    % x \mid \lambda (x:\rulet).e \mid e_1\,e_2 \mid \Lambda \alpha. e \mid e\,\rulet \mid \query \rulet \mid \ilambda \rulet. e \mid e_1 \with e_2 \\
  \eda }

This variant of the syntax splits types into three different sorts:
\emph{context} types, \emph{simple} types and \emph{monotypes}. \emph{Context
types} $\rulet$ correspond to the original types $\rulet$. \emph{Simple types}
$\type$ are a restricted form of context types without toplevel quantifiers and
toplevel implicit arrows. We will see that the distinction between context
types $\rulet$ and simple types $\type$ convenient for measure (1).
\emph{Monotypes} $\suty$ are a further refinement of simple types without
universal quantifiers and implicit arrows anywhere; they help us to implement
measure (3b).

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Revised Resolution Rules}

\newcommand{\elookup}[3][\bar{\alpha}]{{#2}_{#1}\langle{#3}\rangle}
\newcommand{\ivturns}{\mathop{\dot{\turns}_{r}}}

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
          {\bar{\alpha};\tenv;\tenv',\rulet~\gbox{\leadsto x} \ivturns \type~\gbox{\leadsto E[\bar{E}/\bar{x}]}} \\ \\
\mylabel{L-RuleNoMatch} \quad
  \myirule{\not\exists \theta, E, \Sigma, \mathit{dom}(\theta) \subseteq \bar{\alpha}: \theta(\tenv); \theta(\rulet)~\gbox{\leadsto x} \ivturns \theta(\tau)~\gbox{\leadsto E}; \Sigma \\
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
  \myirule{\tenv; \rulet[\suty/\alpha] ~\gbox{\leadsto E\,||\suty||} \ivturns \type~\gbox{\leadsto E'; \Sigma}
           \quad\quad\quad
           \tenv \turns \suty
          }
          {\tenv; \forall \alpha. \rulet ~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma} \\
\ea
$
}
\end{center}
}

Figure~\ref{fig:resolution2} shows our syntax-directed and unambiguous variant
of resolution. 

The main judgement $\env \ivturns \rulet$ is simply a wrapper around the
auxiliary judgement $\bar{\alpha};\env \ivturns \rulet$ that poulates $\bar{\alpha}$
with the type variables in the environment at the point of the query:
\newcommand{\tyvars}[1]{\mathit{tyvars}(#1)}
\begin{equation*}
\begin{array}{rcl@@{\hspace{2cm}}rcl}
\tyvars{\epsilon}     & = & \epsilon &
\tyvars{\tenv,\alpha} & = & \tyvars{\tenv},\alpha \\
\tyvars{\tenv,x : \rulet} & = & \tyvars{\tenv} &
\tyvars{\tenv,\rulet~\gbox{\leadsto x}} & = & \tyvars{\tenv} 
\end{array}
\end{equation*}

The judgement $\bar{\alpha};\tenv \ivturns \rulet$ is syntax-directed (measure (1)) on
$\rulet$. Its job is to strip $\rulet$ down to a simple type $\type$ using
literal copies of the original rules \mylabel{R-TAbs} and \mylabel{R-IAbs}, and
then hand it off to the next judgement in rule \mylabel{R-Simp}.

The next judgement, $\bar{\alpha}; \tenv; \tenv' \ivturns \type$, scans for a
rule type $\rulet$ in the environment $\tenv'$ that matches the simple type
$\type$. Note that we maintain the invariant that $\tenv'$ is a prefix of
$\tenv$ and thus $\rulet \in \tenv$.  The judgement's definition is
syntax-directed on $\tenv'$ (measure (1)) and presents a deterministic
alternative to the original rule \mylabel{R-IVar} by committing to the first
matching rule type (measure (2)). Rules \mylabel{L-Var} and \mylabel{L-TyVar}
skip the irrelevant entries in the environment.  Rule \mylabel{L-RuleMatch}
identifies a matching rule type $\rulet$ with the third auxiliary judgement and
takes care of recursively resolving its context types; details follow below.
Finally, rule \mylabel{L-RuleNoMatch} skips a rule type in the environment if
it does not match. If we take the empty substitution for $\theta$, then the
rule's first condition implies the opposite of rule \mylabel{L-RuleMatch}'s
first condition:
\begin{equation*}
\not\exists \Sigma:\quad\tenv;\rulet \ivturns \type; \Sigma
\end{equation*}
We come back to the reason why the condition is stronger than this in Section~\ref{sec:coherence}.

Finally, the third auxiliary judgement, $\tenv;\rulet \ivturns \type; \Sigma$,
determines whether the rule type $\rulet$ matches the simple type~$\type$. The
judgement is defined by structural induction on $\rulet$, which is step by step
instantiated to a simple type. Any recursive resolutions are deferred in this
process (measure (2b)) -- the postponed resolvents are captured in the $\Sigma$ argument; this
way they do not influence the matching decision and backtracking is avoided.
Instead, the recursive resolutions are executed, as part of rule
\mylabel{L-RuleMatch}, after the rule has been committed to
Rule \mylabel{M-Simp} constitutes the base case where the ruletype equals the
target type. Rule \mylabel{M-IApp} is the counterpart of the original
rule \mylabel{R-IApp} where the impliciation arrow $\rulet_1 \iarrow \rulet_2$
is instantiated to $\rulet_2$; the resolution of $\rulet_1$ is deferred.
Lastly, rule \mylabel{M-TApp} is the couterpart of the original rule \mylabel{R-TApp}.
The main difference is that, in keeping with measure (3b), it only uses
monotypes $\suty$ to substitute the type variable.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Non-Ambiguity Constraints}

TODO

Note that while the rules \mylabel{I-TAbs} and \mylabel{M-TApp} do not explain
how the substitution $[\rulet'/\alpha]$ should be obtained, there is in fact no
ambiguity here. Indeed, there is at most one substitution for which the judgement holds.
Consider the case of matching $\forall \alpha. \alpha \arrow \tyint$ with the
simple type $\tyint \arrow \tyint$. Here the type $\rulet'$ is determined to be
$\tyint$ by the need for $(\alpha \arrow \tyint)[\rulet'/\alpha]$ to be equal to
$\tyint \arrow \tyint$.

However, for the context type $\forall \alpha. \tyint$ ambiguity arises. When
we match the head of this type $\tyint$ with the simple type $\tyint$, the
matching succeeds without actually determining how the type variable $\alpha$
should be instantiated. In fact, the matching succeeds under any possible
substitution of $\alpha$. In this particular case the ambiguity is harmless, because
it does not affect the semantics. Yet, it is not so harmless in other cases.
Take for instance the context type $\forall \alpha. (\alpha \arrow \tystr)
\iarrow (\tystr \arrow \alpha) \iarrow (\tystr \arrow \tystr)$.\footnote{This 
type encodes the well-known ambiguous Haskell type |forall a. (Show a, Read a) => String -> String|
of the expression |read . show|.} Again the
choice of $\alpha$ is ambiguous when matching against the simple type $\tystr
\arrow \tystr$. Yet, now the choice is critical for two reasons. Firstly, if we
guess the wrong instantiation $\rulet$ for $\alpha$, then it may not be possible
to recursively resolve $(\tystr \arrow \alpha)[\alpha/\rulet]$ or $(\alpha \arrow
\tystr)[\alpha/\rulet]$, while with a lucky guess both can be resolved.
Secondly, for different choices of $\rulet$ the types $(\tystr \arrow
\alpha)[\alpha/\rulet]$ and $(\alpha \arrow \tystr)[\alpha/\rulet]$ can be resolved
in completely different ways.

In order to avoid any problems, we conservatively forbid all ambiguous context
types in the implicit environment with the $\epsilon \vdash_{\mathit{unamb}}
\rulet_1$ side-condition in rule \mylabel{Ty-IAbs} of Figure~\ref{fig:type}.\footnote{
An alternative design to avoid such ambiguity would instantiate unused type
variables to a dummy type, like GHC's \texttt{GHC.Prim.Any}, which is only used
for this purpose.}
The definition of $\bar{\alpha} \vdash_{\textit{unamb}}$ is also given in
Figure~\ref{fig:type}. Rule
\mylabel{UA-TAbs} takes care of accumulating the bound type variables
$\bar{\alpha}$ before the head. Rule \mylabel{UA-IAbs} skips over any contexts on the way to the head,
but also recursively requires that these contexts are unambiguous. 
When the head is reached, the central rules \mylabel{UA-TVar} and \mylabel{UA-TFun} check whether
all bound type variables $\bar{\alpha}$ occur in that type.

Finally, the unambiguity condition is also imposed on the queried type $\rulet$ in
rule \mylabel{Ty-Query} because this type too may extend the implicit environment
in rule \mylabel{R-IAbs}.


%-------------------------------------------------------------------------------
\subsection{Coherence Enforcement}\label{sec:coherence}

TODO

In order to enforce coherence, rule \mylabel{L-Tail} makes sure that the
decision to not select a context type is stable under all possible
substitutions $\theta$.  For instance, when looking up |a -> a|, the context
type |Int -> Int| does not match and is skipped. Yet, under the substitution
$\theta = [\alpha \mapsto |Int|]$ the context type would match after all. In
order to avoid this unstable situation, \mylabel{L-Tail} only skips a context
type in the implicit environment, if there is no substitution $\theta$ for
which the type would match the context type.

This approach is similar to that of overlapping type class instances or
overlapping type family instances in Haskell. However, there is one important
complicating factor here: the query type may contain universal qantifiers.
Consider a query for |forall a. a -> a|. In this case we wish to rule out
entirely the context type |Int -> Int| as a potential match. Even though it matches
under the substitution $\theta = [\alpha \mapsto |Int|]$, that covers only one
instantiation while the query requires a resolvent that covers all possible
instantiations at the same time.

In order to bar the set of universally quantified type variables $\bar{\alpha}$ in the query from consideration
for substitution, the matching function $\elookup{\env}{\type}$ is parameterized
by this set. Rule \mylabel{L-Tail}
only considers substitutions $\theta$ whose domain is disjoint from $\bar{\alpha}$.
The two mutually recursive judgements $\bar{\alpha};\env \vturns \rulet$ 
and $\bar{\alpha} \env;\rulet \turns_\downarrow \type$ propagate the universally
quantified type variables $\bar{\alpha}$ to the matching function; rule \tlabel{R-TAbs}
in particular extends $\bar{\alpha}$ whenever going under a universal quantifier.

At the top-level query in rule \mylabel{Ty-Query} the set $\bar{\alpha}$ starts
out empty: $\epsilon;\env \vdash_r \tau$. We typically omit this empty set and
just write $\env \turns_r \tau$ intead.


%   -------------------------------------------------
%   forall b. b -> b, Int -> Int |-r a -> a
%   -------------------------------------------------
%   forall b. b -> b, Int -> Int |-r forall a. a -> a
  


%-------------------------------------------------------------------------------
\subsection{Power of Resolution}

TODO

The rules for deterministic resolution presented in this paper support all the
examples described in Section~\ref{sec:overview}. They are strictly more powerful than
the rules presented in the conference version of the paper~\cite{oliveira12implicit}.
In other words, strictly more queries resolve with this article's rules than
with the rules of the previous paper.
For example, 
the query:

\begin{equation*}
  \tychar \To \tybool,
  \tybool \To \tyint \vturns \tychar \To \tyint
\end{equation*}

\noindent does not resolve under the deterministic resolution rules of
the conference paper. In order to resolve such rule types, it is 
necessary to add the rule type's context to the implicit
environment in the course of the resolution process: 

\begin{equation*}
  \tychar \To \tybool,
  \tybool \To \tyint, \tychar \vturns \tyint
\end{equation*}

\noindent but this was not supported by our previous set of rules. The new set
of resolution rules do support this by means of rule \RIAbs, and queries like
the above can now be resolved.

%-------------------------------------------------------------------------------
\subsection{Algorithm}

\newcommand{\alg}{\turns_{\mathit{alg}}}
\newcommand{\coh}{\turns_{\mathit{coh}}}
\newcommand{\mgu}[3][\bar{\alpha}]{\textit{mgu}_{#1}(#2,#3)}

Figure~\ref{fig:algorithm} contains an algorithm that implements the
non-algorithmic deterministic resolution rules of Figure~\ref{fig:resolution2}.
It differs from the latter in two important ways: 1) it computes rather than
guesses type substitutions, and 2) it replaces explicit enumeration of
substitutions with a tractable approach to coherence checking.

The toplevel relation of the algorithm is $\tenv \alg \rulet$ delegates, in a
similar manner as its declarative counterpart, to the first auxiliary
judgement, $\tyvars{\tenv};\tenv \alg \rulet$, which is also similar to its
declarative counterpart. The main differences are found in the other two
judgements.

TODO

The second major change is that recursive invocations of $\turns_{r}$ are no
longer performed where the recursive contexts $\bar{\rulet}$ are encountered in
the auxiliary relation. Instead, the $\bar{\rulet}$ involved are accumulated and
returned by $\turns_{\mathit{match1st}}$, to be resolved afterwards. In a sense,
we change from a post-order to a pre-order traversal of the conceptual
resolution tree. This change in schedule is an outflow of the change from
guessing to computing context type instantiations, which is explained below.

The two rules for the $\bar{\alpha};\env \turns_{\mathit{match1st}} \tau \hookrightarrow
\bar{\rulet}$ are similar to those of $\elookup{\env}{\tau}=\rulet$: they are set
up to commit to the first matching $\rulet$ in the environment $\env$. The first one is 
defined in terms of the auxiliary relation $\rulet;\bar{\rulet};\bar{\alpha}
\turns_\mathit{match} \tau \rightarrow \bar{\rulet}'$. The latter relation
is the algorithmic counterpart that combines $\rulet \lhd \tau$ and $\bar{\alpha};\env;\rulet \turns_\downarrow \tau$.
As already indicated, the part not included in this relation are the recursive invocations $\bar{\alpha};\env \turns_{r} \rulet_i~(\rulet_i \in \bar{\rulet}')$.
Instead $\bar{\rulet}$ is an accumulating parameter for the $\rulet_i$ so they can be returned in $\bar{\rulet}'$.

Essentially, the relation $\turns_{\mathit{match}}$ peels off the universal
quantifiers and rule contexts from the context type $\rulet$ until it hits the simple
type $\tau'$. The algorithm proceeds in this way because it can compute (rather than guess) the
necessary type instantiation for the universal quantifiers by matching the
context type's head $\tau'$ against the target simple type $\tau$. This
explains why type instantiation is postponed, and, since recursive resolution
depends on type instantiation, also why recursive resolution is postponed even
further. 
\begin{example}
Consider for instance the matching of simple type $\tyint \arrow
\tyint$ against context type $\forall \alpha. \alpha \iarrow (\alpha \arrow
\alpha)$. Just by looking at the outer quantifier $\forall \alpha$ we do not
know what $\alpha$ should be. Hence, we peel off the quantifier, postpone $\alpha$'s instantiation and proceed
with $\alpha \iarrow (\alpha \arrow \alpha)$. At this point, we cannot recursively resolve the context
$\alpha$ because we have not determined $\alpha$ yet. Hence, we must postpone its
resolution and proceed with $\alpha \arrow \alpha$. Now we can determine the substitution
$\theta = [\alpha/\tyint]$ by performing a matching unification with the target simple type $\tyint \arrow \tyint$.
This substitution $\theta$ enables the postponed recursive resolution of $\alpha\theta = \tyint$.
\end{example}

The above informal description is formalized as follows.
There is one rule for each of the three cases: peeling off a context,
peeling off a universal quantifier and handling the simple type $\tau'$:
\begin{enumerate}
\item
As already said, the contexts are collected in the accumulating parameter $\bar{\rulet}$ and
are returned in $\bar{\rulet}'$
\item
In the $\forall \alpha$ rule of $\turns_{\mathit{match}}$ we find the main
difference between the algorithmic and the non-algorithmic definitions. The non-algorithmic definition
\emph{guesses} an appropriate instantiation $\rulet'$ for the type variable $\alpha$, while the algorithmic
definition \emph{computes} this instantiation. This computation does not happen in the $\forall \alpha$ rule;
that rule only accumulates the type variables in the parameter $\bar{\alpha}$ of the relation.
\item
The simple type rule checks whether the target type $\tau$ matches the simple
type $\tau'$. Matching means that the rule checks whether there is a most
general unifier $\theta'$ (see below) of $\tau$ and $\tau'$ whose domain consists only of
the accumulated type variables $\bar{\alpha}$. 
% The ambiguity problem handled by the $\vdash_{\mathit{unamb}}$
% judgement in Figure~\ref{fig:} manifests itself here as the matching unifier $\theta$
% not instantiating all of the 
% type variables $\bar{\alpha}$, because they do not appear in $\tau'$. In order not to introduce any
% unbound type variables, \mylabel{MTC-Simp} rejects this situation by requiring
% that the domain of $\theta$ exactly coincides with $\bar{\alpha}$.
The rule returns the accumulated
contexts $\bar{\rulet}$, but is careful to apply the unifier $\theta$ to them 
in order to take the matching into account.
\end{enumerate}

Finally, the third major change is a tractable approach to enforcing coherence.
It is infeasible to take rule \mylabel{L-Tail} literally and enumerate
infinitely many substitutions. Fortunately, considering all possible
substitutions explicitly is entirely unnecessary. After all, the check $\rulet
\lhd \tau$ essentially considers whether $\tau$ matches the head $\tau'$ of
$\rulet$: \[ \exists \theta. \theta(\tau') = \tau\] We need to establish whether
this check fails for all possible substitutions $\theta'$; in other words, we
want to know whether 
\[ \exists \theta'.\exists \theta. \theta(\theta'(\tau')) = \theta'(\tau) \]
holds. Since the domain of $\theta$ is
disjoint from the free variables of $\tau$, the latter is equivalent to:
\[ \exists \theta'. \exists \theta. \theta(\theta'(\tau')) = \theta(\theta'(\tau)) \]
Of course this is equivalent to the simpler:
\[ \exists \theta. \theta(\tau') = \theta(\tau) \]
which expresses that $\tau$ and $\tau'$ have a most general unifier.
This check is captured in the judgement $\bar{\alpha}; \rulet \vdash_{\mathit{coh}} \tau$,
where $\bar{\alpha}$ are the universally quantified type variables that should not be 
substituted.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Restricted Unification}

Figure~\ref{fig:mgu} lists the algorithm for computing the most general
unifier. For $\theta = \mathit{mgu}_{\bar{\alpha}}(\rulet_1,\rulet_2)$ we
have that $\theta(\rulet_1) = \theta(\rulet_2)$ and $\mathit{dom}(\theta) \subseteq
\bar{\alpha}$. Note that $\bar{\alpha}$ are the variables that are subject to substitution.
Moreover, $\theta$ subsumes any other such unifier. The
algorithm itself is fairly straightforward and needs little explanation.
Only rule \tlabel{UAbs} deserves two notes. Firstly, we assume that $\alpha$-renaming
is used implicitly to use the same name $\beta$ for both bound type variables. Secondly,
we have to be careful that $\beta$ does not escape its scope through $\theta$, which
could happen when computing for example $\mathit{mgu}_{\alpha}(\forall \beta.\beta, \forall \beta.\alpha)$.

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
\multicolumn{1}{c}{\myruleform{\tenv \alg \rulet~\gbox{\leadsto E}}} \\ \\

\mylabel{AR-Main}\quad
\myirule{\mathit{tyvars}(\tenv);\tenv \alg \rulet~\gbox{\leadsto E}}
        {\tenv \alg \rulet~\gbox{\leadsto E}}  \\ \\

\multicolumn{1}{c}{\myruleform{\bar{\alpha};\tenv \alg \rulet~\gbox{\leadsto E}}} \\ \\

\mylabel{AR-IAbs}\quad
\myirule{\bar{\alpha};\tenv, \rulet_1~\gbox{\leadsto x} \alg \rulet_2~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
        {\bar{\alpha};\tenv \alg \rulet_1 \iarrow \rulet_2 ~\gbox{\leadsto \lambda(x : ||\rulet_1||). E}} \quad\quad\quad

\mylabel{AR-TAbs}\quad
\myirule{\bar{\alpha};\tenv,\alpha \alg \rulet ~\gbox{\leadsto E}}
        {\bar{\alpha};\tenv \alg \forall \alpha. \rulet ~\gbox{\leadsto \Lambda \alpha. E}}  \\ \\

% \mylabel{Alg-Simp}\quad
% \myirule{\bar{\alpha};\tenv \turns_{\mathit{match1st}} \tau \hookrightarrow \bar{\rulet}\gbox{; \bar{\omega}; E} \quad\quad \bar{\alpha};\tenv \alg \rulet_i~\gbox{\leadsto E_i} \quad (\forall \rulet_i \in \bar{\rulet})}
%         {\bar{\alpha};\tenv \alg \tau ~\gbox{\leadsto E[\bar{\omega}/\bar{E}]} }  \\ \\

\mylabel{AR-Simp}\quad
\myirule{\bar{\alpha};\tenv;\tenv \alg \tau~\gbox{\leadsto E}}
        {\bar{\alpha};\tenv \alg \tau ~\gbox{\leadsto E} }  \\ \\

\multicolumn{1}{c}{\myruleform{\bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E} }} \\ \\

\mylabel{AL-RuleMatch}\quad
\myirule{\epsilon; \tenv; \rulet~\gbox{\leadsto x}; \epsilon \alg \type~\gbox{\leadsto E}; \bar{\rulet}~\gbox{\leadsto \bar{x}} \quad\quad
         \bar{\alpha};\tenv \alg \bar{\rulet}~\gbox{\leadsto \bar{E}}}
        {\bar{\alpha};\tenv; \tenv', \rulet~\gbox{\leadsto x} \alg \type~\gbox{\leadsto E[\bar{E}/\bar{x}] }}  \\ \\

\mylabel{AL-RuleNoMatch}\quad
\myirule{\bar{\alpha};\rulet \not\coh \type \quad\quad
         \bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E'}}
        {\bar{\alpha};\tenv;\tenv', \rulet~\gbox{\leadsto x}\alg \type~\gbox{\leadsto E'}}  \\ \\
\mylabel{AL-Var} \quad
  \myirule{\bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E}
          }
          {\bar{\alpha};\tenv;\tenv',x:\rulet \alg \type~\gbox{\leadsto E}} 
\quad\quad\quad
\mylabel{AL-TyVar} \quad
  \myirule{\bar{\alpha};\tenv;\tenv' \alg \type~\gbox{\leadsto E}
          }
          {\bar{\alpha};\tenv;\tenv',\alpha \alg \type~\gbox{\leadsto E}} 
\\ \\ \\

\multicolumn{1}{c}{\myruleform{\alpha; \tenv; \rulet~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}} \\ \\

\mylabel{AM-Simp}\quad
\myirule{\theta = \textit{mgu}_{\bar{\alpha}}(\type,\type')
        }
        {\bar{\alpha}; \tenv; \type'~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto ||\theta||(E)}; \theta(\Sigma)}  \\ \\

\mylabel{AM-IApp}\quad
\myirule{\bar{\alpha}; \tenv, \rulet_1~\gbox{\leadsto x}; \rulet_2~\gbox{\leadsto E\,x}; \rulet_1~\gbox{\leadsto x}, \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'\quad\quad \gbox{x~\mathit{fresh}}}
        {\bar{\alpha}; \tenv; \rulet_1 \iarrow \rulet_2~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}  \\ \\

\mylabel{AM-TApp}\quad
\myirule{\bar{\alpha},\alpha; \tenv; \rulet~\gbox{\leadsto E\,\alpha}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}
        {\bar{\alpha}; \tenv; \forall \alpha. \rulet~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}  \\ \\


\multicolumn{1}{c}{\myruleform{\bar{\alpha};\rulet\coh \tau}} \\ \\
\mylabel{COH-TAbs}\quad
\myirule{\bar{\alpha},\alpha;\rulet \coh \tau}
        {\bar{\alpha};\forall \alpha. \rulet\coh \tau}  \quad\quad\quad
\mylabel{COH-IAbs}\quad
\myirule{\bar{\alpha};\rulet_2 \coh \tau}
        {\bar{\alpha};\rulet_1 \iarrow \rulet_2\coh \tau}  \\ \\
\mylabel{COH-Simp}\quad
\myirule{\theta = \textit{mgu}_{\bar{\alpha}}(\tau,\tau')
        }
        {\bar{\alpha};\tau'\coh \tau}  \\ \\
\ea
$
}
\end{center}
}

\figtwocol{fig:mgu}{Most General Unifier}{
\begin{center}
\framebox{$
\ba{c}
\multicolumn{1}{c}{\myruleform{\theta = \mathit{mgu}_{\bar{\alpha}}(\rulet_1,\rulet_2)}} \\ \\

\mylabel{UInstL}\quad\myirule{ \alpha \in \bar{\alpha}
        } 
        { [\suty/\alpha] = \mathit{mgu}_{\bar{\alpha}}(\alpha,\suty)} \hspace{1cm} 

\mylabel{UInstR}\quad\myirule{ \alpha \in \bar{\alpha}
        } 
        { [\suty/\alpha] = \mathit{mgu}_{\bar{\alpha}}(\suty,\alpha)} \\ \\

\mylabel{UVar}\quad
\myirule{
        } 
        { \emptyset = \mathit{mgu}_{\bar{\alpha}}(\beta,\beta)}  \\ \\

\mylabel{UFun}\quad
\myirule{\theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rulet_{1,1},\rulet_{2,1})
         \quad\quad
         \theta_2 = \mathit{mgu}_{\bar{\alpha}}(\theta_1(\rulet_{1,2}),\theta_1(\rulet_{2,2}))
        } 
        {\theta_2 \cdot \theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rulet_{1,1} \arrow \rulet_{1,2},\rulet_{2,1} \arrow \rulet_{2,2})}  \\ \\


\mylabel{URul}\quad
\myirule{\theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rulet_{1,1},\rulet_{2,1})
         \quad\quad
         \theta_2 = \mathit{mgu}_{\bar{\alpha}}(\theta_1(\rulet_{1,2}),\theta_1(\rulet_{2,2}))
        } 
        {\theta_2 \cdot \theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rulet_{1,1} \iarrow \rulet_{1,2},\rulet_{2,1} \iarrow \rulet_{2,2})}  \\ \\

\mylabel{UAbs}\quad
\myirule{\theta = \mathit{mgu}_{\bar{\alpha}}(\rulet_{1},\rulet_{2})
          \quad\quad
          \beta \not\in \mathit{ftv}(\theta)
        } 
        {\theta = \mathit{mgu}_{\bar{\alpha}}(\forall \beta.\rulet_{1},\forall \beta.\rulet_{2})}  \\ \\
\ea
$
}
\end{center}
}

%===============================================================================

%-------------------------------------------------------------------------------
\subsection{Termination of Resolution}

TODO

If we are not careful about which rules are added to the implicit environment, then
the resolution process may not terminate.
This section describes how to impose 
a set of modular syntactic restrictions that prevents non-termination. 
%% We have to avoid non-termination of the type checker to ensure soundness.

As an example of non-termination consider 
\begin{equation*}
  \tychar \To \tyint,
  \tyint \To \tychar \vturns \tyint
\end{equation*}
which loops, using alternatively the first and second rule in the implicit
environment. The source of this non-termination are the mutually recursive 
definitions of the $\vturns$ and $\turns_\downarrow$ relations: a type is resolved
in terms of a rule type whose head it matches, but this requires further 
resolution of the rule type's body. 

\newcommand{\term}[1]{\turns_\mathit{term} #1}
\newcommand{\occ}[2]{\mathit{occ}_{#1}(#2)}
\newcommand{\tnorm}[1]{\||#1\||}

\subsubsection{Termination Condition}
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

One potential problem is that the size measure does not properly take into
account universally quantified type variables. It assigns them size 1 but
ignores the fact that the size may increase dramatically when the type variable
is instantiated with a large type. The rule $\TermRule$ makes up for this problem
by requiring a size decrease for all possible instantiations of free type variables.
However, rather than to specify this property non-constructively as 
\[ \forall \bar{\rulet}. \||[\bar{\alpha}\mapsto\bar{\rulet}]\tau_1\|| < \||[\bar{\alpha}\mapsto\bar{\rulet}]\tau_2\|| \]
it provides a more practical means to verify this condition by way of free variable occurrences.
The number of occurrences $\occ{\alpha}{\tau_1}$ of free variable $\alpha$ in type $\tau_1$ should be less than the number
of occurrences 
$\occ{\alpha}{\tau_2}$ in $\tau_2$. It is easy to see that the non-constructive property follows from this requirement.

\subsubsection{Integration in the Type System}
There are various ways to integrate the termination condition in the type system. 
The most generic approach is to require that all types satisfy the termination condition.
This can be done by making the condition part of the well-formedness relation for types.


\figtwocol{fig:termination}{Termination Condition}{
\begin{center}
\framebox{
\begin{minipage}{.81\textwidth}
$
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
           \rulet_1 \lhd \tau_1 \quad\quad \rulet_2 \lhd \tau_2 \quad\quad \tnorm{\tau_1} < \tnorm{\tau_2} \\
           \forall \alpha \in \ftv{\rulet_1} \cup \ftv{\rulet_2}: \quad \occ{\alpha}{\tau_1} \leq \occ{\alpha}{\tau_2}}  
          {\term{\rulet_1 \iarrow \rulet_2}} 
\\ \\
\ea
$
    \begin{eqnarray*}
      \occ{\alpha}{\tyint} & = & 0 \\
      \occ{\alpha}{\beta} & = & \left\{ \begin{array}{ll} 
         1 & \hspace{1cm}(\alpha = \beta) \\
         0 & \hspace{1cm}(\alpha \neq \beta)
         \end{array}\right. \\
      \occ{\alpha}{\rulet_1 \arrow \rulet_2} & = & \occ{\alpha}{\rulet_1} + \occ{\alpha}{\rulet_2} \\
      \occ{\alpha}{\rulet_1 \iarrow \rulet_2} & = & \occ{\alpha}{\rulet_1} + \occ{\alpha}{\rulet_2} \\
      \occ{\alpha}{\forall \beta.\rulet} & = & \occ{\alpha}{\rulet} \\ \\
      \tnorm{\tyint} & = & 1 \\
      \tnorm{\alpha} & = & 1 \\
      \tnorm{\rulet_1 \arrow \rulet_2} & = & 1 + \tnorm{\rulet_1} + \tnorm{\rulet_2} \\
      \tnorm{\rulet_1 \iarrow \rulet_2} & = & 1 + \tnorm{\rulet_1} + \tnorm{\rulet_2} \\
      \tnorm{\forall \alpha.\rulet} & = & \tnorm{\rulet}
    \end{eqnarray*} 
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
% $\ourlang$, termination of resolution coincides with the traditional program
% termination problem. So, alternatively, $\ourlang$  may enforce termination in
% a less stringent manner using available termination checkers like~\cite{approve}.

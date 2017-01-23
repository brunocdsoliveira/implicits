%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Rule.fmt

\newcommand{\rhs}[1]{\mathit{rhs}(#1)}
\newcommand{\lhs}[1]{\mathit{lhs}(#1)}
\newcommand{\qtv}[1]{\mathit{qtv}(#1)}
\newcommand{\ftv}[1]{\mathit{ftv}(#1)}

%%\renewcommand{\cdot}{\emptyset}

\section{The $\ourlang$ Calculus}
\label{sec:ourlang}

This section formalizes the syntax and type system of $\ourlang$.  In
Section~\ref{sec:trans} (building on top of this type system) we will present
the formalization of the type-directed translation to System F. However, to
avoid duplication and facilitate readability, we present the rules of the
type system and type-directed translation together. We use grey boxes 
to indicate parts of the rules which belong to the type-directed 
translation. These greyed parts will be explained in Section~\ref{sec:trans} and 
can be ignored in the remainder of this section.

%-------------------------------------------------------------------------------
\subsection{Syntax}    
\label{subsec:syntax}

%%if False

This is the syntax of the calculus:
{\bda{llrl}
    \text{Types} & \rho  & ::=  & \alpha \mid \rulet_1 \arrow \rulet_2 \mid \forall \alpha. \rulet \mid \rulet_1 \iarrow \rulet_2 \\
%    \text{Types} & \rulesetvar \hide{\in 2^\meta{RType}} & ::= & 
%    \bar{\rulet} \\
    \text{Expressions} & |e| & ::=  &
     x \mid \lambda (x:\rulet).e \mid e_1\,e_2 \mid \Lambda \alpha. e \mid e\,\rulet \mid \query \rulet \mid \ilambda \rulet. e \mid e_1 \with e_2  \\
  \eda }

%%endif



\textit{Types} $\rho$ comprise four constructs: type variables
$\alpha$; function types $\rulet_1 \arrow \rulet_2$; type abstraction
$\forall \alpha. \rulet$; and the novel rule type $\rulet_1 \iarrow
\rulet_2$.  In a rule type $\rulet_1 \iarrow \rulet_2$, type $\rulet_1$ is
called the \textit{context} and type $\rulet_2$ the \textit{head}.

Expressions $e$ include three
abstraction-eliminination pairs. The
binder $\lambda (x:\rulet). e$ abstracts expression $e$ over values of type $\rulet$, is eliminated by
application $e_1\,e_2$ and refers to the bound value with variable $x$.
The binder $\Lambda \alpha.e$ abstracts expression $e$ over types, is eliminated
by type application $e\,\rho$ and refers to the bound type with type variable $\alpha$ 
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

\[ | implicit {-"\overline{"-} e : {-"\rho}"-} in e1 == ({-" \overline{\lambda_? \rho .} "-} e1) {-"\overline{"-} with e {-"}"-} | \]
%}\bruno{Also introduce let, which is used later, in the translation.}

The notation $\overline{\lambda_? \rho .}$ is a shortform for 
$\lambda_? \rho_1.~\ldots~\lambda_? \rho_n.$. Correspondingly,
the notation $\overline{|with|~e}$ is a shortform for
|with| $e_1 \ldots $ |with| $e_n$.

% For readability purposes, when we use |implicit| we omit the type annotation 
% |tau|. As we shall see in Section~\ref{sec:example} this annotation can be 
% automatically inferred.

For brevity, we have kept $\ourlang$ small. Examples
may use additional syntax such as built-in integers, integer operators and boolean
literals and types. 
% Extending this calculus with support for \emph{higher-kinded 
% polymorphism} in the style of System $F_{\omega}$ is not hard.  
% The implementation
% of the source language (and $\ourlang$) presented in
% Section~\ref{sec:example} implements various of these extensions.

%-------------------------------------------------------------------------------

\subsection{Type System}
\label{sec:types}

\figtwocol{fig:type}{Type System and Type-directed Translation to System F}{
\begin{center}
\framebox{
\begin{minipage}{\textwidth}
\bda{c}
\multicolumn{1}{c}{\myruleform{\tenv \turns \rulet}} \\ \\

%%\WFIntTy \quad
%%  \myirule{}{\tenv \turns \tyint} \quad\quad\quad
\WFVarTy \quad
  \myirule{ \alpha \in \tenv }
          { \tenv \turns \alpha } \quad\quad\quad
\WFFunTy \quad
  \myirule{\tenv \turns \rho_1 \quad\quad \tenv \turns \rho_2}
          {\tenv \turns \rho_1 \arrow \rho_2} \\ \\
\WFAbsTy \quad
  \myirule{ \tenv, \alpha \turns \rho} %% \quad\quad \alpha \in \ftv{\rho}
          { \tenv \turns \forall\alpha.\rho } \quad\quad\quad
\WFRulTy \quad
  \myirule{\tenv \turns \rho_1 \quad\quad \tenv \turns \rho_2} % \quad\quad \ftv{\rho_1} \subseteq \ftv{\rho_2}}
          {\tenv \turns \rho_1 \iarrow \rho_2}
\eda

\bda{lc} 

& \multicolumn{1}{c}{
  \myruleform{\tenv \turns \relation{e}{\rulet}~\gbox{\leadsto E}}} \\
\\
%%\TyInt &
%%{ \tenv \mid \denv \turns \relation{n}{\tyint}~\gbox{\leadsto n} } 
%%\\ \\

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
  \myirule {  \tenv,\alpha \turns \relation{e}{\rho}~\gbox{\leadsto E_1} 
              \quad\quad\quad
              \alpha \not\in \tenv \quad\quad\quad 
           }
           { \tenv \turns \relation{\Lambda \alpha.e}{\forall
               \alpha.\rho}~\gbox{\leadsto \Lambda \alpha.E_1} } \quad\quad\quad
\\ \\
\TyTApp&
  \myirule { \tenv \turns \relation{e}{\forall \alpha.\rho_2}~\gbox{\leadsto E}
              \quad\quad\quad
              \tenv \turns \rulet_1 
           }
           { \tenv \turns \relation{e\,\rho_1}{\rho_2 [\rho_1 /\alpha]}~\gbox{\leadsto
    E~||\rho_1||}} 
\\ \\
\TyIAbs&
  \myirule { \tenv, \rho_1 \gbox{\leadsto x} \turns \relation{e}{\rho_2}~\gbox{\leadsto
    E} 
             \quad \tenv \turns \rulet_1 
             \quad \epsilon \vdash_{\mathit{unamb}} \rulet_1
             \quad \gbox{x~\mathit{fresh}}}
           { \tenv \turns \relation{\ilambda \rho_1.e}{\rho_1 \iarrow \rho_2}~\gbox{\leadsto
    \lambda \relation{x}{||\rulet_1||}. E}}
\\ \\
\TyIApp&
  \myirule { \tenv \turns \relation{e_1}{\rho_2 \iarrow
      \rho_1~\gbox{\leadsto E_1}} 
             \quad\quad\quad
             \tenv \turns \relation{e_2}{\rho_2}~\gbox{\leadsto E_2}}
           { \tenv \turns \relation{e_1 \with e_2}{\rho_1}~\gbox{\leadsto
    E_1~E_2}}
\\ \\
\TyQuery &
\myirule
{ \tenv \vturns \rulet~\gbox{\leadsto E} \quad\quad\quad \tenv \turns \rulet \quad\quad\quad \epsilon \vdash_{\mathit{unamb}} \rulet}
{ \tenv \turns \relation{?\rulet}{\rulet}~\gbox{\leadsto E}
} 
\eda
\bda{c}
\myruleform{\bar{\alpha} \vdash_{\mathit{unamb}} \rho} \\ \\
\mylabel{UA-TAbs} \quad
\myirule{\bar{\alpha},\alpha \vdash_{\mathit{unamb}} \rho}
        {\bar{\alpha} \vdash_{\mathit{unamb}} \forall \alpha.\rho} 
\quad\quad\quad
\mylabel{UA-IAbs} \quad
\myirule{\epsilon \vdash_{\mathit{unamb}} \rho_1 \quad\quad \bar{\alpha} \vdash_{\mathit{unamb}} \rho_2}
        {\bar{\alpha} \vdash_{\mathit{unamb}} \rho_1 \iarrow \rho_2} \\ \\
\mylabel{UA-TAbsAlt} \quad
\myirule{\bar{\alpha} \vdash_{\mathit{unamb}} \rho}
        {\bar{\alpha} \vdash_{\mathit{unamb}} \forall \alpha.\rho}
\quad\quad\quad
\mylabel{UA-IAbsAlt} \quad
\myirule{\epsilon \vdash_{\mathit{unamb}} \rho_1 \quad\quad \bar{\alpha},\mathit{ftv}(\rho_1) \vdash_{\mathit{unamb}} \rho_2}
        {\bar{\alpha} \vdash_{\mathit{unamb}} \rho_1 \iarrow \rho_2} \\ \\
\mylabel{UA-Simp} \quad
\myirule{\bar{\alpha} \subseteq \mathit{ftv}(\type)}
        {\bar{\alpha} \vdash_{\mathit{unamb}} \type}
\quad\quad\quad
\text{TODO: postpone until $\type$ is introduced}
\eda
\end{minipage}
}
\end{center}
}\bruno{If we want the more relaxed unambiguity check, then I think the rules are incorrect. What we wish to enforce
is that all type variables used in contexts are also used in the head. That is we want to accept $\forall \alpha. Int$.
I've written alternative rules for the relaxed checking.}
\bruno{Another point I remember discussing with Philip is whether the unambiguity check can be combined with termination
checking. Should we consider this option?}

%Type System~Figure

%if False

\figtwocol{fig:type}{Type System}{
\begin{center}
\framebox{
$\ba{c} 
\multicolumn{1}{c}{\myruleform{\tenv \turns \rulet}} \\ \\

\WFIntTy \quad
  \myirule{}{\tenv \turns \tyint} \quad\quad\quad
\WFVarTy \quad
  \myirule{ \alpha \in \tenv }
          { \tenv \turns \alpha } \quad\quad\quad
\WFFunTy \quad
  \myirule{\tenv \turns \rho_1 \quad\quad \tenv \turns \rho_2}
          {\tenv \turns \rho_1 \arrow \rho_2} \\ \\
\WFAbsTy \quad
  \myirule{ \tenv, \alpha \turns \rho \quad\quad \alpha \in \ftv{\rho}}
          { \tenv \turns \forall\alpha.\rho } \quad\quad\quad
\WFRulTy \quad
  \myirule{\tenv \turns \rho_1 \quad\quad \tenv \turns \rho_2 \quad\quad \ftv{\rho_1} \subseteq \ftv{\rho_2}}
          {\tenv \turns \rho_1 \iarrow \rho_2}
\\ \\
\multicolumn{1}{c}{\myruleform{\tenv\mid\env \turns \relation{e}{\rho}}} \\ \\

\TyInt \quad
  { \tenv\mid\env \turns \relation{n}{\tyint} } \quad\quad\quad
\TyVar \quad
  \myirule { (x:\rho) \in \tenv }
           { \tenv\mid\env \turns \relation{x}{\rho} } 
\\ \\

\TyTAbs\quad
  \myirule { \alpha \in \ftv{\rulet} \\ \tenv,\alpha \mid \env \turns \relation{e}{\rho} }
           { \tenv\mid\env \turns \relation{\Lambda \alpha.e}{\forall \alpha.\rho} } \quad\quad\quad
\TyTApp\quad
  \myirule { \tenv \turns \rulet \\ \tenv\mid \env \turns \relation{e}{\forall \alpha.\rho'} }
           { \tenv\mid\env \turns \relation{e\,\rulet}{\rho'[\rulet/\alpha]} } 
\\ \\

\TyAbs \quad
  \myirule { \tenv \turns \rulet_1 \\ \tenv,\relation{x}{\rho_1}\mid \env \turns \relation{e}{\rho_2} }
           { \tenv\mid\env \turns \relation{\lambda \relation{x}{\rho_1}.e}{\rho_1 \arrow \rho_2} } \quad\quad\quad
\TyIAbs\quad
  \myirule {  \tenv \turns \rulet_1 \\ \tenv \mid \env, \rho_1 \turns \relation{e}{\rho_2} }
           { \tenv\mid\env \turns \relation{\ilambda \rho_1.e}{\rho_1 \iarrow \rho_2} }
\\ \\

\TyApp \quad
  \myirule { \tenv\mid \env \turns \relation{e_1}{\rho_2 \arrow \rho_1} \\
             \tenv\mid \env \turns \relation{e_2}{\rho_2} }
           { \tenv\mid\env \turns \relation{e_1\,e_2}{\rho_1} } \quad\quad\quad
\TyIApp\quad
  \myirule { \tenv \mid \env \turns \relation{e_1}{\rho_2 \iarrow \rho_1} \\
             \tenv \mid \env \turns \relation{e_2}{\rho_2}}
           { \tenv\mid\env \turns \relation{e_1 \with e_2}{\rho_1} }
\\ \\

\multicolumn{1}{c}{
\TyQuery \quad
\myirule
{ \tenv \turns \rho \quad\quad \env \vturns \rho
  % \quad \shade{\unambiguous(\rulet)}
}
{ \tenv\mid \env \turns \relation{?\rho}{\rho} }  }
% 
% \TyRule &
% \myirule
% { \rulet = \rulesch{\alpha}{\rulesetvar}{\type} \quad
%   \shade{\unambiguous(\rulet)} \\
%   \tenv\mid \env, \rulesetvar \turns \relation{e}{\type} \quad
%   \vec{\alpha} \cap \mathit{ftv}(\tenv,\env) = \emptyset
% }
% { \tenv\mid \env \turns \relation{\ruleabs{\rulet}{e}}{\rulet}
% } 
% \\ \\
% 
% \TyInst &
% \myirule
% { \tenv\mid \env \turns 
%   \relation{e}{\rulesch{\alpha}{\rulesetvar}{\type}}
% }
% { \tenv\mid \env \turns
%   \relation{e[\vec{\type}]}
%   {\subst{\vec{\alpha}}{\vec{\type}}(\rulesetvar \To \type)}
% }
% \\ \\
% 
% \TyRApp &
% \myirule
% { \tenv\mid \env \turns \relation{e}{\ruleset \To \type} \\
%   \tenv\mid \env \turns \relation{e_i}{\rulet_i} \quad
%   (\forall \relation{e_i}{\rulet_i} \in
%   \overline{\relation{e}{\rulet}})
%   % \\
%   % \shade{\distinctwith(\rulesetexp)}
% }
% { \tenv\mid \env \turns 
%   \relation{(\ruleapp{e}{\rulesetexp})}{\type}
% } \\ \\
\ea
$
}
\end{center}
}

%endif

Figure \ref{fig:type} presents the static type system of $\ourlang$. The type system 
is based on the type system of System F, and every System F term is typeable in our 
system.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Well-Formed Types}
The judgement $\tenv \turns \rulet$ denotes
the well-formedness of types with respect to type environment $\tenv$. A
type environment $\tenv$ records the type variables $\alpha$ 
and the variables $x$ with associated type $\rulet$ in scope:
\bda{llrl} 
\text{Type Environments}     & \tenv & ::= & \epsilon \mid \tenv, \relation{x}{\rulet} \mid \tenv , \alpha \mid \tenv, \rulet~\gbox{\leadsto x} \\
\eda
Types $\rho$ are well-formed iff their free type variables occur in the type
environment $\WFVarTy$.
% , and, in the case of rule types $\rulet_1 \iarrow \rulet_2$, iff the
% free type variables in the context $\rulet_1$ are a subset of those in the head
% $\rulet_2$ $\WFRulTy$. The second condition avoids types like |forall a. a => Int|.
% Haskell has a similar condition like the later to avoid
% qualified types like |C a => Int|\footnote{A well-known example is |(show . read) :: forall a. (Show a, Read a) => String|}, and
% the former cannot be expressed syntactically in Haskell'98. In both cases the head does not determine
% the type variable |a|, which may thus be ambiguously chosen. To avoid this
% ambiguity, types of this form are forbidden.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Well-Typed Expressions}
The typing judgment ${\tenv\mid\env\turns\relation{e}{\rho}}$ means that
expression $e$ has type $\rho$ under type environment $\tenv$ and implicit
environment $\env$. The implicit environment $\env$ is defined as:
\bda{llrl} 
\text{\st{Implicit Environments}} & \env  & ::= & \epsilon \mid \env , \rulet~\gbox{\leadsto x} \\
\eda

Most of the rules are entirely standard; only three deserve special attention.
Firstly, rule \TyIAbs{} extends the implicit environment with the type of an implicit value. 
The side condition $\epsilon \vdash_{\mathit{unamb}} \rho$ states that
the type $\rho_1$ must be unambiguous; we explain this concept in Section~\ref{subsec:det}.
Secondly, rule \TyIApp{} eliminates an implicit abstraction by supplying a 
value of the required type. Finally, rule \TyQuery{} resolves 
a particular unambiguous type $\rho$ against the implicit environment.
It is defined in terms of the auxiliary judgement $\env \vturns \rho$, which
is explained next.

% We will not discuss the first four rules ($\TyInt$, $\TyVar$, $\TyAbs$ and $\TyApp$) because they
% are entirely standard. For now we also ignore the grey-shaded conditions in the other rules;
% they are explained in Section~\ref{sec:conditions}.

% Rule $\TyRule$ checks a rule abstraction $\ruleabs{\rulesch{\alpha}{\rulesetvar}{\type}}{e}$ by checking
% whether the rule's body $e$ actually has the type $\type$ under the assumed
% implicit type context $\bar{\rulet}$. Rule $\TyInst$ instantiates a rule
% type's type variables $\vec{\alpha}$ with the given types $\vec{\type}$,
% and rule $\TyRApp$ instantiates the type context $\bar{\rulet}$ with expressions
% of the required rule types $\overline{\relation{e}{\rulet}}$.
% Finally, rule $\TyQuery$ delegates queries directly to the resolution rule $\StaRes$.
% 
% $\env \vturns \rulet$
% expresses that type $\rulet$ is resolvable with respect to $\env$.
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
            \lambda\relation{x}{||\rho_1||}.E}} 
\\ \\
\mylabel{R-IApp} \quad
  \myirule{\tenv \vturns \rulet_1 \iarrow \rulet_2~\gbox{\leadsto E_2} \quad\quad \tenv \vturns \rulet_1~\gbox{\leadsto E_1}}
          {\tenv \vturns \rulet_2~~\gbox{\leadsto E_2~E_1}}
\\ \\


% \StaRes &
% \myirule
% { \lookup{\env}{\type} = \rulesetvar' \Rightarrow \type \\
%   \env \vturns \rulet_i \quad 
%   (\forall \rulet_i \in \rulesetvar' - \rulesetvar)
%   % \\
%   % \shade{\coherent(\env,\type)} \quad
%   % \shade{\disjoint(\rulesetvar'',\rulesetvar)} \quad
%   % \shade{\distinctctx(\rulesetvar'')}
% }
% { \env \vturns \rulesch{\alpha}{\rulesetvar}{\type}
% } \\ \\
% 
% \eda
% 
% \bda{llc}
% 
% \myruleform{\lookup{\env}{\type} = \rulet} & & 
% \myirule
% {
%   \lookup{\rulesetvar}{\type} = \rulet \quad\quad \shade{\textsf{no\_overlap}(\rulesetvar,\type)}
% }
% {
%   \lookup{(\env;\rulesetvar)}{\type} = \rulet
% } \\ \\
% & &
% \myirule
% {
%   \lookup{\rulesetvar}{\type} = \bot \quad 
%   \lookup{\env}{\type} = \rulet
% }
% {
%   \lookup{(\env;\rulesetvar)}{\type} = \rulet
% } \\ \\ 
% 
% \myruleform{\lookup{\rulesetvar}{\type} = \rulet} & &
%  \myirule
% {
%   \rulet \in \rulesetvar \quad\quad \rulet = \forall\vec{\alpha}'.\rulesetvar'\To\type' \quad\quad
%   \theta\type' = \type 
% }
% {
%   \lookup{\rulesetvar}{\type} = \theta\rulesetvar' \Rightarrow \type
% } 

\ea
$
}
\end{center}
}


The underlying principle of resolution in $\ourlang$ originates
from resolution in logic. 
Intuitively, $\env\vdash_r \rho$ holds if $\env$ entails $\rho$, where the types in $\env$ and
$\rho$ are read as propositions.
Following the Curry-Howard correspondence, we read
$\alpha$ as a propositional variable, $\forall \alpha.\rho$ as universal quantification, and
rule types $\rho_1 \iarrow \rho_2$ as implication. We do not give a special interpretation to
the function type $\rho_1 \arrow \rho_2$, treating it as an uninterpreted predicate.
Unlike traditional Curry-Howard, we have two forms of arrow, functions and rules,
and the important twist on the traditional correspondence is that we choose to treat
rules as implications, leaving functions as uninterpreted predicates.

% Following the Curry-Howard correspondence,
% we assign to each type a corresponding logical interpretation.
% % with the $(\cdot)^\dagger$ function:
% % \begin{definition}[Logical Interpretation]
% % \begin{eqnarray*}
% % \alpha^\dagger & = & \alpha^\dagger \\
% % \tyint^\dagger & = & \tyint^\dagger \\
% % (\rulet_1 \rightarrow \rulet_2)^\dagger & = & \rulet_1^\dagger \rightarrow^\dagger \rulet_2^\dagger \\
% % (\rulet_1 \iarrow \rulet_2)^\dagger     & = & \rulet_1^\dagger \iarrow \rulet_2^\dagger \\
% % (\forall \alpha.\rulet)^\dagger        & = & \forall \alpha^\dagger.\rulet^\dagger
% % % (\forall \vec{\alpha}.\rulesetvar \To \type)^\dagger & = & \forall \vec{\alpha}^\dagger . \bigwedge_{\rho \in \rulesetvar} \rho^\dagger \To \type^\dagger
% % \end{eqnarray*}
% % \end{definition}
% Here, type variables $\alpha$ map to propositional variables.  Unlike
% Curry-Howard, we do not map function types to logical implications; we
% deliberately restrict our implicational reasoning to rule types. So, instead we
% also map the function arrow to an uninterpreted higher-order predicate.
% Finally, as already indicated, we map rule types to logical implications. 
% Resolution in $\ourlang$ then corresponds to checking entailment of the logical
% interpretation.
% % We postulate this property as a theorem that constrains the design of resolution.
% % % and encourage the reader to verify that it is satisfied by $\StaRes$.
% % \begin{theorem}[Resolution Specification] \ 
% % \begin{center}
% % If $\env \vturns \rulet$, then $\env^\dagger \models \rulet^\dagger$.
% % \end{center}
% % \end{theorem}

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
% \mylabel{R-IVar}\ \ 
% \myirule{\tyint \in (\tyint,\tybool,\tybool\iarrow\tyint)}
%         {\tyint,\tybool,\tybool\iarrow\tyint \vturns \tyint}
% \quad\quad\quad
% \mylabel{R-IAbs}\ \ \myirule{\mylabel{R-IVar}\ \ \myirule{\tybool \in (\tyint,\tybool,\tybool\iarrow\tyint)}{\tyint,\tybool,\tybool\iarrow\tyint \vturns \tybool}}
%         {\tyint,\tybool,\tybool\iarrow\tyint \vturns \tyint}
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
% \mylabel{R-IVar}\ \ 
% \myirule{\tyint \in (\tyint,\tybool,\tybool\iarrow\tyint)}
%         {\tyint,\tybool,\tybool\iarrow\tyint \vturns \tyint}
% \quad\quad\quad
% \mylabel{R-IAbs}\ \ \myirule{\mylabel{R-IVar}\ \ \myirule{\tybool \in (\tyint,\tybool,\tybool\iarrow\tyint)}{\tyint,\tybool,\tybool\iarrow\tyint \vturns \tybool}}
%         {\tyint,\tybool,\tybool\iarrow\tyint \vturns \tyint}
\end{array}
\end{equation*}
While this may seem harmless at the type-level, at the value-level each
derivation corresponds with a (possibly) different value. Hence, ambiguous
resolution renders the meaning of a program ambiguous.
\end{enumerate}

%-------------------------------------------------------------------------------
\subsection{Deterministic Resolution}\label{subsec:det}

To help define deterministic resolution, we provide a variant of the syntax of the calculus:

{\bda{llrl}
    \text{Simple Types} & \type  & ::=  & \alpha \mid \rulet_1 \arrow \rulet_2 \\
    \text{Context Types} & \rulet \hide{\in 2^\meta{RType}} & ::= & 
    \forall \alpha. \rulet \mid \rulet_1 \iarrow \rulet_2 \mid \type \\
    \textcolor{blue}{\text{Substitution Types}} & \suty & ::=  & \alpha \mid \suty \arrow \suty
    % \text{Expressions} & |e| & ::=  &
    % x \mid \lambda (x:\rulet).e \mid e_1\,e_2 \mid \Lambda \alpha. e \mid e\,\rulet \mid \query \rulet \mid \ilambda \rulet. e \mid e_1 \with e_2 \\
  \eda }
\bruno{Should we call substitution types, monotypes instead?}

This variant of the syntax splits types into \emph{simple} types and \emph{context} types. 
\textit{Simple types} $\type$ comprise two type constructs (type variables
$\alpha$ and function types $\rulet_1 \arrow \rulet_2$). 
\textit{Context types} $\rulet$ comprise the types which participate in the 
(recursive) resolution of rules. The type abstraction $\forall \alpha. \rulet$
as well as the \emph{rule types} $\rulet_1 \iarrow \rulet_2$ are the main 
constructs, while other (simple) types act as base cases in the resolution process. 
Expressions remain unchanged.

% \bruno{Had to remove $\Theta$ (singleton environment) to unify the figures.}

\newcommand{\elookup}[3][\bar{\alpha}]{{#2}_{#1}\langle{#3}\rangle}
\newcommand{\ivturns}{\mathop{\dot{\turns}_{r}}}

\figtwocol{fig:resolution2}{Deterministic Resolution and Translation to System F}{
\begin{center}
\framebox{$
\ba{c}
\Sigma ::= \epsilon \mid \Sigma, \rulet~\gbox{\leadsto x} \\ \\
\multicolumn{1}{c}{\myruleform{\tenv \ivturns \rho~\gbox{\leadsto E}}} \\ \\
\mylabel{R-Main} \quad
  \myirule{\mathit{tyvars}(\tenv);\tenv \ivturns \rulet~\gbox{\leadsto E}}
          {\tenv \ivturns \rulet~\gbox{\leadsto E}} \\ \\
\multicolumn{1}{c}{\myruleform{\bar{\alpha}; \tenv \ivturns \rho~\gbox{\leadsto E}}} \\ \\
%%\quad\quad\quad
\mylabel{R-IAbs} \quad
  \myirule{\bar{\alpha};\tenv, \rho_1~\gbox{\leadsto x} \ivturns \rho_2~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
          {\bar{\alpha};\tenv \ivturns \rho_1 \iarrow \rho_2~\gbox{\leadsto
            \lambda\relation{x}{||\rho_1||}.E}} 
\quad\quad
\mylabel{R-TAbs} \quad
  \myirule{\bar{\alpha};\tenv,\alpha \ivturns \rho~\gbox{\leadsto E}}
          {\bar{\alpha};\tenv \ivturns \forall \alpha. \rho~\gbox{\leadsto \Lambda\alpha.E}} 
\\ \\
\mylabel{R-Simp} \quad
 \myirule{\bar{\alpha};\tenv;\tenv \ivturns \type~\gbox{\leadsto E}}
         {\bar{\alpha};\tenv \ivturns \type~\gbox{\leadsto E}} 
\\ \\ \\
\myruleform{\bar{\alpha};\tenv;\tenv' \ivturns \type~\gbox{\leadsto E}}\\ \\

\mylabel{L-RuleMatch} \quad
  \myirule{\tenv; \rulet~\gbox{\leadsto x} \ivturns \tau~\gbox{\leadsto E}; \overline{\rulet~\gbox{\leadsto x}} \\
            \bar{\alpha};\tenv \ivturns \bar{\rho}~\gbox{\leadsto \bar{E}}
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
\mylabel{M-IAbs} \quad
  \myirule{\tenv, \rulet_1 \gbox{\leadsto x}; \rulet_2 ~\gbox{\leadsto E\,x} \ivturns \type~\gbox{\leadsto E'}; \Sigma 
           \quad\quad\quad \gbox{x~\mathit{fresh}}
          }
          {\tenv; \rulet_1 \iarrow \rulet_2 ~\gbox{\leadsto E} \ivturns \type~\gbox{\leadsto E'}; \Sigma, \rulet_1~\gbox{\leadsto x}} \\ \\ 
\mylabel{M-TAbs} \quad
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

%if False

\figtwocol{fig:resolution2}{Deterministic Resolution}{
\begin{center}
\framebox{$
\ba{c}
\multicolumn{1}{c}{\myruleform{\env \vturns \rho}} \\ \\

\mylabel{R-TAbs} \quad  \myirule{\env \vturns \rho}
          {\env \vturns \forall \alpha. \rho} 
\quad\quad
\mylabel{R-IAbs}\quad  \myirule{\env, \rho_1 \vturns \rho_2}
          {\env \vturns \rho_1 \iarrow \rho_2} 
\quad\quad
\mylabel{R-Simp}\quad \myirule{\env\langle\type\rangle = \rho \quad\quad \env; \rho \turns_\downarrow \type}
          {\env \vturns \type} 
\\ \\
\myruleform{\env; \rho \turns_\downarrow \type} \\ \\
\mylabel{I-Simp} \quad  \myirule{}
          {\env; \type \turns_\downarrow \type}  
\quad\quad
\mylabel{I-TAbs} \quad  \myirule{\env; \rho[\rulet'/\alpha] \turns_\downarrow \type}
          {\env; \forall \alpha.\rho \turns_\downarrow \type}  
\quad\quad
\mylabel{I-IAbs} \quad \myirule{\env \vturns \rho_1 \quad\quad \env; \rho_2 \turns_\downarrow \type}
          {\env; \rho_1 \iarrow \rho_2 \turns_\downarrow \type}  
\\ \\
\myruleform{\env\langle\type\rangle = \rho} \\ \\
\mylabel{L-Head} \quad  \myirule{\rho \lhd \type}
          {(\env,\rho)\langle\type\rangle = \rho}  
\quad\quad\quad
\mylabel{L-Tail} \quad \myirule{\rho'' \mathop{\not\!\!\lhd} \type \quad\quad \env\langle\type\rangle = \rho'}
          {(\env,\rho'')\langle\type\rangle = \rho'}  
\\ \\
\myruleform{\rho\lhd\type} \\ \\
\mylabel{M-Simp} \quad   \myirule{}
          {\type \lhd \type}
\quad\quad\quad
\mylabel{M-TAbs} \quad \myirule{\rho[\rulet'/\alpha] \lhd \type}
          {\forall \alpha.\rho \lhd \type}
\quad\quad\quad
\mylabel{M-IAbs} \quad \myirule{\rho' \lhd \type}
          {\rho'' \iarrow \rho' \lhd \type}
\ea
$
}
\end{center}
}

%endif

To solve the two problems Figure~\ref{fig:resolution2} shows a syntax-directed and 
unambiguous variant of resolution. 
The main judgement $\bar{\alpha};\env \vturns \rulet$ is defined by
mutual recursion with the auxiliary judgement $\bar{\alpha};\env;\rulet \turns_\downarrow \type$.
The former judgement handles proper context types $\rulet$ in the obvious way
and delegates to the latter judgement for simple types $\type$. Note that the 
stratification of types into context and simple types makes all rules syntax-directed.

Rule types $\rho_1 \Rightarrow \rho_2$ are resolved by pushing $\rho_1$ 
to the implicit environment and then resolving $\rho_2$ under that environment 
\mylabel{R-IAbs}. Type abstractions $\forall \alpha. \rho$ are resolved by peeling off 
the universal quantifier and then resolving $\rho$ against the implicit environment \mylabel{R-TAbs}. 
A simple type $\type$ is resolved in terms of the \emph{first} matching context type
$\rulet$ found in the implicit environment $\mylabel{R-Simp}$. The bias towards the first avoids ambiguity when
there are multiple matching context type.

The partial function $\env\langle\type\rangle$ returns the
\emph{first} matching context type found in the implicit environment.
Whether a context type $\rulet$
matches a simple type $\type$ is defined by $\rulet \lhd \type$.  In essence, a
context type matches a simple type if the simple type is an instance of its
right-most head. 

The judgement $\bar{\alpha};\env;\rulet \turns_\downarrow \type$ is defined by three rules
that mirror the three rules of the judgement $\rulet \lhd \type$. These rules
peel off from left to right the universal quantifiers and rule contexts
until the target simple type is obtained: 
\begin{itemize}
\item Universal quantifiers are eliminated by means of appropriate instantiation \mylabel{I-TAbs}. 
      Note that thanks to the well-formedness condition on types, the type instantiation
      is unambiguous.
\item Contexts are eliminated by means of recursive resolution \mylabel{I-IAbs}.
\end{itemize}

Note that while the rules \mylabel{I-TAbs} and \mylabel{M-TAbs} do not explain
how the substitution $[\rho'/\alpha]$ should be obtained, there is in fact no
ambiguity here. Indeed, there is at most one substitution for which the judgement holds.
Consider the case of matching $\forall \alpha. \alpha \arrow \tyint$ with the
simple type $\tyint \arrow \tyint$. Here the type $\rho'$ is determined to be
$\tyint$ by the need for $(\alpha \arrow \tyint)[\rho'/\alpha]$ to be equal to
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
guess the wrong instantiation $\rho$ for $\alpha$, then it may not be possible
to recursively resolve $(\tystr \arrow \alpha)[\alpha/\rho]$ or $(\alpha \arrow
\tystr)[\alpha/\rho]$, while with a lucky guess both can be resolved.
Secondly, for different choices of $\rho$ the types $(\tystr \arrow
\alpha)[\alpha/\rho]$ and $(\alpha \arrow \tystr)[\alpha/\rho]$ can be resolved
in completely different ways.

In order to avoid any problems, we conservatively forbid all ambiguous context
types in the implicit environment with the $\epsilon \vdash_{\mathit{unamb}}
\rho_1$ side-condition in rule \mylabel{Ty-IAbs} of Figure~\ref{fig:type}.\footnote{
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

Finally, the unambiguity condition is also imposed on the queried type $\rho$ in
rule \mylabel{Ty-Query} because this type too may extend the implicit environment
in rule \mylabel{R-IAbs}.

%-------------------------------------------------------------------------------
\subsection{Coherence Enforcement}

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

Figure~\ref{fig:algorithm} contains an algorithm that implements the
non-algorithmic deterministic resolution rules of Figure~\ref{fig:resolution2}.
It differs from the latter in three important ways: 1) it computes rather than
guesses type substitutions, 2) it traverses a context type at most once per
matching and 3) it replaces explicit enumeration of substitutions with a
tractable approach to coherence checking.

The toplevel relation of the algorithm is $\bar{\alpha}; \env \turns_{\mathit{alg}} \rho$; it
implements the non-algorithmic $\bar{\alpha}; \env \turns_{r} \rho$ relation. The relation
is defined in a syntax-directed manner, with one rule for each of the three
possible forms of $\rho$. The first two of these three rules are essentially
identical to the corresponding two rules of $\turns_{r}$. 

The last rule, for the form $\tau$, differs significantly in the algorithm.
Essentially, it captures the two relations $\elookup{\env}{\tau} = \rho$ and
$\bar{\alpha}; \env;\rho\turns_\downarrow \tau$ into the single $\bar{\alpha};\env
\turns_{\mathit{match1st}} \tau \hookrightarrow \bar{\rho}$. The two traversals
of the intermediate rule type $\rho$ are thereby replaced by a single
traversal. This avoids the need to compute the instantiation of the context
type $\mathit{\rho}$ twice.

The second major change is that recursive invocations of $\turns_{r}$ are no
longer performed where the recursive contexts $\bar{\rho}$ are encountered in
the auxiliary relation. Instead, the $\bar{\rho}$ involved are accumulated and
returned by $\turns_{\mathit{match1st}}$, to be resolved afterwards. In a sense,
we change from a post-order to a pre-order traversal of the conceptual
resolution tree. This change in schedule is an outflow of the change from
guessing to computing context type instantiations, which is explained below.

The two rules for the $\bar{\alpha};\env \turns_{\mathit{match1st}} \tau \hookrightarrow
\bar{\rho}$ are similar to those of $\elookup{\env}{\tau}=\rho$: they are set
up to commit to the first matching $\rho$ in the environment $\env$. The first one is 
defined in terms of the auxiliary relation $\rho;\bar{\rho};\bar{\alpha}
\turns_\mathit{match} \tau \rightarrow \bar{\rho}'$. The latter relation
is the algorithmic counterpart that combines $\rho \lhd \tau$ and $\bar{\alpha};\env;\rho \turns_\downarrow \tau$.
As already indicated, the part not included in this relation are the recursive invocations $\bar{\alpha};\env \turns_{r} \rho_i~(\rho_i \in \bar{\rho}')$.
Instead $\bar{\rho}$ is an accumulating parameter for the $\rho_i$ so they can be returned in $\bar{\rho}'$.

Essentially, the relation $\turns_{\mathit{match}}$ peels off the universal
quantifiers and rule contexts from the context type $\rho$ until it hits the simple
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
As already said, the contexts are collected in the accumulating parameter $\bar{\rho}$ and
are returned in $\bar{\rho}'$
\item
In the $\forall \alpha$ rule of $\turns_{\mathit{match}}$ we find the main
difference between the algorithmic and the non-algorithmic definitions. The non-algorithmic definition
\emph{guesses} an appropriate instantiation $\rho'$ for the type variable $\alpha$, while the algorithmic
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
contexts $\bar{\rho}$, but is careful to apply the unifier $\theta$ to them 
in order to take the matching into account.
\end{enumerate}

Finally, the third major change is a tractable approach to enforcing coherence.
It is infeasible to take rule \mylabel{L-Tail} literally and enumerate
infinitely many substitutions. Fortunately, considering all possible
substitutions explicitly is entirely unnecessary. After all, the check $\rho
\lhd \tau$ essentially considers whether $\tau$ matches the head $\tau'$ of
$\rho$: \[ \exists \theta. \theta(\tau') = \tau\] We need to establish whether
this check fails for all possible substitutions $\theta'$; in other words, we
want to know whether 
\[ \exists \theta'.\exists \theta. \theta(\theta'(\tau')) = \theta'(\tau) \]
holds. Since the domain of $\theta$ is
disjoint from the free variables of $\tau$, the latter is equivalent to:
\[ \exists \theta'. \exists \theta. \theta(\theta'(\tau')) = \theta(\theta'(\tau)) \]
Of course this is equivalent to the simpler:
\[ \exists \theta. \theta(\tau') = \theta(\tau) \]
which expresses that $\tau$ and $\tau'$ have a most general unifier.
This check is captured in the judgement $\bar{\alpha}; \rho \vdash_{\mathit{coh}} \tau$,
where $\bar{\alpha}$ are the universally quantified type variables that should not be 
substituted.

\paragraph{Restricted Unification}
Figure~\ref{fig:mgu} lists the algorithm for computing the most general
unifier. For $\theta = \mathit{mgu}_{\bar{\alpha}}(\rho_1,\rho_2)$ we
have that $\theta(\rho_1) = \theta(\rho_2)$ and $\mathit{dom}(\theta) \subseteq
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

\newcommand{\alg}{\turns_{\mathit{alg}}}
\newcommand{\coh}{\turns_{\mathit{coh}}}
\newcommand{\mgu}[3][\bar{\alpha}]{\textit{mgu}_{#1}(#2,#3)}

\figtwocol{fig:algorithm}{Resolution Algorithm}{
\begin{center}
\framebox{$
\ba{c}
\multicolumn{1}{c}{\myruleform{\tenv \alg \rho~\gbox{\leadsto E}}} \\ \\

\mylabel{AR-Main}\quad
\myirule{\mathit{tyvars}(\tenv);\tenv \alg \rho~\gbox{\leadsto E}}
        {\tenv \alg \rho~\gbox{\leadsto E}}  \\ \\

\multicolumn{1}{c}{\myruleform{\bar{\alpha};\tenv \alg \rho~\gbox{\leadsto E}}} \\ \\

\mylabel{AR-IAbs}\quad
\myirule{\bar{\alpha};\tenv, \rho_1~\gbox{\leadsto x} \alg \rho_2~\gbox{\leadsto E} \quad\quad \gbox{x~\mathit{fresh}}}
        {\bar{\alpha};\tenv \alg \rho_1 \iarrow \rho_2 ~\gbox{\leadsto \lambda(x : ||\rho_1||). E}} \quad\quad\quad

\mylabel{AR-TAbs}\quad
\myirule{\bar{\alpha};\tenv,\alpha \alg \rho ~\gbox{\leadsto E}}
        {\bar{\alpha};\tenv \alg \forall \alpha. \rho ~\gbox{\leadsto \Lambda \alpha. E}}  \\ \\

% \mylabel{Alg-Simp}\quad
% \myirule{\bar{\alpha};\tenv \turns_{\mathit{match1st}} \tau \hookrightarrow \bar{\rho}\gbox{; \bar{\omega}; E} \quad\quad \bar{\alpha};\tenv \alg \rho_i~\gbox{\leadsto E_i} \quad (\forall \rho_i \in \bar{\rho})}
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

\mylabel{AM-IAbs}\quad
\myirule{\bar{\alpha}; \tenv, \rulet_1~\gbox{\leadsto x}; \rulet_2~\gbox{\leadsto E\,x}; \rulet_1~\gbox{\leadsto x}, \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'\quad\quad \gbox{x~\mathit{fresh}}}
        {\bar{\alpha}; \tenv; \rulet_1 \iarrow \rulet_2~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}  \\ \\

\mylabel{AM-TAbs}\quad
\myirule{\bar{\alpha},\alpha; \tenv; \rulet~\gbox{\leadsto E\,\alpha}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}
        {\bar{\alpha}; \tenv; \forall \alpha. \rulet~\gbox{\leadsto E}; \Sigma \alg \type~\gbox{\leadsto E'}; \Sigma'}  \\ \\


\multicolumn{1}{c}{\myruleform{\bar{\alpha};\rho\coh \tau}} \\ \\
\mylabel{COH-TAbs}\quad
\myirule{\bar{\alpha},\alpha;\rho \coh \tau}
        {\bar{\alpha};\forall \alpha. \rho\coh \tau}  \quad\quad\quad
\mylabel{COH-IAbs}\quad
\myirule{\bar{\alpha};\rho_2 \coh \tau}
        {\bar{\alpha};\rho_1 \iarrow \rho_2\coh \tau}  \\ \\
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
\multicolumn{1}{c}{\myruleform{\theta = \mathit{mgu}_{\bar{\alpha}}(\rho_1,\rho_2)}} \\ \\

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
\myirule{\theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rho_{1,1},\rho_{2,1})
         \quad\quad
         \theta_2 = \mathit{mgu}_{\bar{\alpha}}(\theta_1(\rho_{1,2}),\theta_1(\rho_{2,2}))
        } 
        {\theta_2 \cdot \theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rho_{1,1} \arrow \rho_{1,2},\rho_{2,1} \arrow \rho_{2,2})}  \\ \\


\mylabel{URul}\quad
\myirule{\theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rho_{1,1},\rho_{2,1})
         \quad\quad
         \theta_2 = \mathit{mgu}_{\bar{\alpha}}(\theta_1(\rho_{1,2}),\theta_1(\rho_{2,2}))
        } 
        {\theta_2 \cdot \theta_1 = \mathit{mgu}_{\bar{\alpha}}(\rho_{1,1} \iarrow \rho_{1,2},\rho_{2,1} \iarrow \rho_{2,2})}  \\ \\

\mylabel{UAbs}\quad
\myirule{\theta = \mathit{mgu}_{\bar{\alpha}}(\rho_{1},\rho_{2})
          \quad\quad
          \beta \not\in \mathit{ftv}(\theta)
        } 
        {\theta = \mathit{mgu}_{\bar{\alpha}}(\forall \beta.\rho_{1},\forall \beta.\rho_{2})}  \\ \\
\ea
$
}
\end{center}
}

% 
% 
% \subsection{Old explanation of Resolution - needs revising/integration}
% 
% 
% \paragraph{Resolution for Simple Types}
% The step from the logical interpretation to the $\StaRes$ rule in
% Figure~\ref{fig:type} is non-trivial. So, let us first look
% at a simpler incarnation. What does resolution look like for simple
% types $\type$ like $\tyint$? 
% \begin{equation*}
% \SimpleRes~~~~~
% \myirule
% { \lookup{\env}{\type} = \rulesetvar' \Rightarrow \type  \\
%   \env \vturns \rulet_i \quad 
%   (\forall \rulet_i \in \rulesetvar')
% }
% { \env \vturns \type
% }
% ~~~~~\phantom{\SimpleRes}
% \end{equation*}
% First, it looks up a \textit{matching} rule type in the implicit environment by
% means of the lookup function $\lookup{\env}{\type}$ defined in
% Fig.~\ref{fig:type}.  This partial function respects the nested scopes: it
% first looks in the topmost context of the implicit environment, and, only if it
% does not find a matching rule, does it descend. Within an environment context,
% the lookup function looks for a rule type whose right-hand side $\type'$ can be
% instantiated to the queried $\type$ using a matching unifier $\theta$. This rule
% type is then returned in instantiated form.
% 
% The matching expresses that the looked-up rule produces a value of the required
% type.  To do so, the looked-up rule may itself require other implicit values.
% This requirement is captured in the context $\rulesetvar'$, which must
% be resolved recursively. Hence, the resolution rule is
% itself a recursive rule. When the context $\rulesetvar'$ of the looked-up
% rule is empty, a base case of the recursion has been reached.
% 
% \begin{example}
% Consider this query for a tuple of integers:  \[\tyint; \ruleschr{\alpha}{\{
% \alpha \}}{\alpha \times \alpha} \vturns \tyint \times \tyint\] Lookup yields
% the second rule, which produces a tuple, instantiated to $\{ \tyint \}
% \Rightarrow \tyint \times \tyint$ with matching substitution $\theta = [\alpha
% \leadsto \tyint]$. In order to produce a tuple, the rule requires a
% value of the component type. Hence, resolution proceeds by recursively querying
% for $\tyint$. Now lookup yields the first rule, which
% produces an integer, with empty matching substitution and no further
% requirements.
% \end{example}
% 
% \paragraph{Resolution for Rule Types}
% So far, so good. Apart from allowing any types, recursive querying for simple
% types is quite similar to recursive type class resolution, and $\ourlang$
% carefully captures the expected behavior. However, what is distinctly novel in
% $\ourlang$, is that it also provides \textit{resolution of rule types}, which
% requires a markedly different treatment.
% \begin{equation*}
% \RuleRes~~~~~
% \myirule
% { \lookup{\env}{\type} = \rulesetvar \Rightarrow \type
% }
% { \env \vturns \rulesch{\alpha}{\rulesetvar}{\type}
% }
% ~~~~~\phantom{\RuleRes}
% \end{equation*}
% Here we retrieve a whole rule from the environment, including its context.
% Resolution again performs a lookup based on a matching right-hand side $\type$,
% but subsequently also matches the context with the one that is queried. No recursive
% resolution takes place.
% \begin{example}
% Consider a variant of the above query:  
% \[\tyint; \ruleschr{\alpha}{\{ \alpha \}}{\alpha \times \alpha} \vturns \{ \tyint \} \Rightarrow \tyint \times \tyint\] 
% Again lookup yields the second rule, instantiated to $\{ \tyint \}
% \Rightarrow \tyint \times \tyint$. The context $\{ \tyint \}$ of this rule
% matches the context of the queried rule. Hence, the query is resolved without
% recursive resolution.
% \end{example}
% 
% 
% \paragraph{Unified Resolution}
% The feat that our actual resolution rule $\StaRes$ accomplishes is to unify
% these seemingly disparate forms of resolution into one single inference rule.
% In fact, both $\SimpleRes$ and $\RuleRes$ are special cases of $\StaRes$, which
% provides some additional expressiveness in the form of \textit{partial
% resolution} (explained below).
% 
% The first hurdle for $\StaRes$ is that types $\type$ and rule types $\rulet$
% are different syntactic categories. Judging from its definition, $\StaRes$ only covers rule types.
% How do we get it to treat simple types then?  Just promote the simple
% type $\type$ to its corresponding rule type
% $\ruleschr{}{\{\}}{\type}$ and $\StaRes$ will do what we expect
% for simple types, including recursive resolution. At the same time, it still
% matches proper rule types exactly, without recursion, when that is appropriate.
% 
% Choosing the right treatment for the context is the second hurdle. This part is
% managed by recursively resolving $\rulesetvar' - \rulesetvar$. In the case of
% promoted simple types, $\rulesetvar$ is empty, and the whole of $\rulesetvar'$
% is recursively solved; which is exactly what we want. In the case
% $\rulesetvar'$ matches $\rulesetvar$, no recursive resolution takes place.
% Again this perfectly corresponds to what we have set out above for proper rule
% types. However, there is a third case, where $\rulesetvar' - \rulesetvar$ is a
% non-empty proper subset of $\rulesetvar'$. We call this situation, where part of the
% retrieved rule's context is recursively resolved and part is not,
% \textit{partial resolution}.
% 
% \begin{example}
% Here is another query variant:  
% \[\tybool; \ruleschr{\alpha}{\{ \tybool, \alpha \}}{\alpha \times \alpha}
% \vturns \{ \tyint \} \Rightarrow \tyint \times \tyint\] 
% The first lookup yields the second rule, instantiated to $\{ \tybool, \tyint \}
% \Rightarrow \tyint \times \tyint$, which almost matches the queried rule type.
% Only $\tybool$ in the context is unwelcome, so it is eliminated through a recursive
% resolution step. Fortunately, the first rule in the environment is available for that.
% \end{example}
%  
% %-------------------------------------------------------------------------------
% \subsection{Additional Type System Conditions}\label{sec:conditions}
% 
% The gray-shaded conditions in the type system are to check lookup
% errors ($\textsf{no\_overlap}$) % (\distinctwith, \distinctctx, and \disjoint) 
% and ambiguous
% instantiations (\unambiguous). 
% % and coherence failures (\coherent)
% % discussed in Section~\ref{subsec:error}.
% 
% \paragraph{Avoiding Lookup Errors} To prevent lookup failures, we
% have to check for two situations:
% 
% \begin{itemize}
% 
% \item A lookup has no matching rule in the environment.
% 
% \item A lookup has multiple matching rules which have different rule
%   types but can yield values of the same type (overlapping
%   rules).
% 
% % \item A lookup has multiple matching rules which have the exact same
% %  rule type but different values (overlapping rule sets).
% 
% \end{itemize}
% The former condition is directly captured in the definition of lookup
% among a set of rule types. The latter condition is captured in the
% $\textsf{no\_overlap}$ property, which is defined as:
% \begin{equation*}
% \begin{array}{lcclcl}
%  \multicolumn{6}{l}{\textsf{no\_overlap}(\{\rulet_1,\ldots,\rulet_n\},\type) 
%   \defeq} \\
% ~~~ & \forall i, j. &        & \rulet_i = \rulesch{\alpha_i}{\rulesetvar_i}{\type_i} & \wedge & \exists \theta_i. \theta_i\type_i = \type  \\
%     &               & \wedge & \rulet_j = \rulesch{\alpha_j}{\rulesetvar_j}{\type_j} & \wedge & \exists \theta_j. \theta_j\type_j = \type  \\
%     & & \Longrightarrow & ~ i = j
% \end{array}
% \end{equation*}
% 
% % The first two cases are taken care of by our definition of lookup in
% % the type environment. The last case is taken care of by the following
% % three conditions:
% 
% % \begin{itemize}
% % \item $\distinctwith(\rulesetexp).$ In \TyRApp, we have to check whether
% %   a rule set expression $\rulesetexp$ has overlaps.
% %   For example, rule set expression |{3 :
% %     Int, 4 : Int}| consists of an overlapping rule set because it has
% %   different expressions with the same type, though the corresponding
% %   context |{Int}| has no overlap. 
% %   % We should also reject rule set
% %   % expressions like |{3 : Int, (query a) : a}|, where an overlapping
% %   % rule set can be generated once the type variable |a| is instantiated
% %   % to |Int|. The \distinctwith{} condition is true when there are no two
% %   % rule types that can become the same after instantiation:
% %   \begin{equation*}
% %     \distinctwith(\relation{e_1}{\rulet_1},\ldots,\relation{e_n}{\rulet_n}) \defeq 
% %     \distinctctx(\rulet_1,\ldots,\rulet_n)
% %     % \forall \myrelation{e_1}{\rulet_1},
% %     % \myrelation{e_2}{\rulet_2} \in \rulesetexp.
% %     % \forall \theta. \theta \rulet_1 \neq \theta \rulet_2.
% %   \end{equation*}
% 
% % \item $\distinctctx(\rulesetvar'').$ In \StaRes, we have to check if
% %   an overlapping rule set can be generated during the partial
% %   resolution of the context $\rulesetvar''$, Hence, the 
% %   \distinctctx{} condition's definition is
% %   \begin{equation*} 
% %     \distinctctx(\rulet_1,\ldots,\rulet_n) \defeq
% %     \forall i,j. i \neq j \Rightarrow
% %     \forall \theta. \theta \rulet_i \neq \theta \rulet_j.
% %   \end{equation*}
% % 
% % \item $\disjoint(\rulesetvar'', \rulesetvar).$ In \StaRes, we have to
% %   check if the partially-resolved context $\rulesetvar''$ and the
% %   remaining one $\rulesetvar$ can overlap. Hence, the \disjoint{} is
% %   defined as
% %   \begin{align*}
% %     \disjoint(\rulesetvar_1,\rulesetvar_2) & \defeq
% %     \forall \rulet_1 \in \rulesetvar_1.\forall \rulet_2 \in
% %     \rulesetvar_2. \forall \theta. \theta \rulet_1 \neq \theta
% %     \rulet_2.
% %   \end{align*}
% %   
% %   To see why this \disjoint{} condition is necessary, consider the
% %   following example:
% %   \[|tstate turns (query (forall a.{a} => Pair Int a)) eval v|\]
% %   where
% %   \vspace{-5mm}
% %   \begin{align*}
% %     |tstate| = & ~ 
% %     |{Int : 3, rulet : {-"\rclos{\rulet,-,-,\nil}"-}}| \\
% %     |rulet| = & ~ |forall a.{a,Int} => Pair Int a| \\
% %     |v| = & ~ \rclos{|forall a.{a} => Pair Int a|,-,-,|{Int:3}|}.
% %   \end{align*}
% %   The value |v| is the result of query $|forall a.{a} => Pair Int a|$,
% %   which is generated from the value $\rclos{\rulet, -,-,\nil}$ by
% %   partially resolving |Int| in the context of $\rulet$ (|{a,
% %     Int}|). Thus, the value |v| has partially-resolved rule set |{Int
% %     : 3}|.  If the type variable |a| in the closure |v| is
% %   instantiated to type |Int| and the value is applied to a rule set
% %   $\eta$ of context |{Int}|, for example, |{Int : 4}|, then the rule
% %   set can overlap the partially-resolved rule set |{Int : 3}| of
% %   |v|. The $\disjoint$ condition fails in this case because
% %   $\rulesetvar'' = |{Int}|$ and $\rulesetvar = |{a}|$ and these can
% %   overlap each other by substitution $\subst{\alpha}{\tyint}$.
% % 
% % \end{itemize}
% 
% % \paragraph{Avoiding Coherence Failures}
% % To avoid coherence failures, we have to check two things. First, we
% % need to check the existence of a single, lexically nearest
% % match. Second, we need to check if the nearest match is actually used
% % for all queries at runtime. The first check is done by our lookup
% % operator on type environment ($\lookup{\env}{\type}$). The second one
% % is taken care of by the following condition \coherent:
% % \begin{equation*}
% %   \coherent(\env,\type) \defeq
% %   \forall \theta. \theta (\lookup{\env}{\type}) = 
% %   \lookup{(\theta \env)}{\theta\type}.
% % \end{equation*}
% % The condition requires that the static lookup result (image of
% % $\env$ for $\tau$ without considering any instantiation) is always
% % the same as the one that we get at runtime (image of $\theta\env$
% % for $\tau$ with its instantiation $\theta\tau$) modulo runtime type
% % information $\theta$.
% % 
% % Please note that our language respects
% % \textit{parametricity}~\cite{parametricity} as a consequence of the
% % $\coherent$ condition. Because of the condition, the behavior of
% % resolution does not depend on any runtime type information. The
% % following example, based on~\cite{blame}, illustrates what happens without parametricity:
% % \[|
% % tstate turns let f : forall a.a -> a = fun (x) ((?a->a) x) in f<#Int#> 1 eval 2
% % |\] 
% % where 
% % $| tstate = {forall b.b->b:(rclos id)}; {Int->Int: (rclos inc)}|$.
% % 
% % According to parametricity, function $f$ can only be the
% % identity function. However, when |a| is instantiated to |Int|, it
% % actually behaves like an increment function. This violation of
% % parametricity is dangerous for all kinds of program transformations
% % based on free theorems~\cite{Wadler89theoremsfor}.  The \coherent{}
% % condition rejects the above program, as for $\theta = [\beta \leadsto
% % |Int|]$ we have that
% % \begin{equation*}
% %   \theta(\env(\beta \rightarrow \beta)) = |forall
% %   a . a -> a| \neq |Int -> Int| = (\theta \env)(\theta(\beta \rightarrow
% %   \beta)),
% % \end{equation*}
% % where $\env = \myset{|forall a. a -> a|}; \myset{|Int -> Int|}$.
% 
% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
% % \paragraph{Coherent Query}
% % For static resolution to be sound, we need to ensure that all queries
% % instantiated from the original query by substitution are successfully
% % resolved. Because the query that the static resolution receives is the
% % one without any type variable instantiated, while the query might be
% % instantiated to a concrete type when it reaches a resolution point in
% % operational semantics. We guarantee this by the condition \coherent{},
% % whose definition is like this:
% % \[
% %   \coherent(\env,\type) \defeq
% %   \forall \theta. \theta(\env(\type)) = (\theta \env)(\theta\type)
% % \]
% % % \footnote{Actual definition is more complex: We annotate type
% % % environment entities with corresponding stack level, and check not only equivalence
% % % of types but also annotations. Type level information alone is too coerce to capture
% % % runtime behavior properly.}
% % The condition means that the result without knowing the exact query
% % ($\theta \env(\type)$) should be always the same as the one that we
% % get during dynamic resolution ($(\theta \env)(\theta \type)$). This
% % essentially rules out all ambiguous lookup due to overlapping contexts.
% 
% % Overlapping contexts, which are allowed in Haskell, can be 
% % modeled in $\ourlang$ using nested scoping. In Section 5, we will explain 
% % how to encode overlapping contexts.
% 
% % Note that the following program is accepted:
% % > let f = rule (forall a b.{a,b} => (Pair a b)) (((query a),(query b)))
% % > in (f [int,int], f [int, bool])
% % The context $|{a,b}|$ is unambiguous because, there is no
% % overlapping at runtime, to whatever type $|a|$ and $|b|$ are instantiated. 
% % If two types are instantiated to the same type, they will be coereced
% % into one because contexts are a set.
% 
% % % into stack of contexts without 
% % %overlapping.
% 
% % Having coherent condition, we know that the behavior of the resolution
% % does not depend on any runtime type information since the lookup
% % yields the same result both in dynamic and static resolution. In other
% % words, our language respects
% % \textit{parametricity}~\cite{parametricity}.  To illustrate what
% % happens without parametricity, we recast the example presented in
% % Section~\ref{sec:intro} to $\ourlang$ syntax:
% 
% % % > let f : forall b.b -> b =
% % % >   implicit {fun (x) (x) : forall a. a -> a} in 
% % % >     implicit {fun (n) (n + 1) : Int -> Int} in 
% % % >       query (b -> b)
% 
% % > rule (forall b. b -> b) ((rule ({forall a. a -> a} => b -> b) ((rule ({Int -> Int} => b -> b) (query (b -> b))
% % >      with {fun n (n + 1) : Int -> Int}))
% % >      with {fun x x : forall a.a -> a}))
% 
% % \noindent
% % If we are to believe parametricity, this program can only be the
% % identity function. However, when |b| is instantiated to |Int|, it
% % actually behaves like an increment function! This is of course very
% % dangerous for all kinds of program transformations based on free
% % theorems~\cite{Wadler89theoremsfor}.
% 
% % The \coherent{} condition rejects the above program, as for $\theta =
% % [\beta \leadsto |Int|]$ we have that $\theta(\env(\beta \rightarrow
% % \beta)) = |forall a . a -> a| \neq |Int -> Int| = (\theta
% % \env)(\theta(\beta \rightarrow \beta))$, where $\env = \myset{|forall
% %   a. a -> a|}; \myset{|Int -> Int|}$.
% 
% %\bruno{The following needs to be finidhed!}
% %\bruno{Also it appears that this part is discussed below again. 
% %Starting from paragraph ``Rule (StaRes) uses disjoint ...''. }
% %The $\coherent{}$ condition also prevents lookup failure due to overlapping types
% %within type environment. Therefore, succefull static resolution implies
% 
% %\paragraph{Query}
% %Rule $\TyQuery$ checks if the type environment is
% %\textit{well-defined} in addition to performing static resolution. A
% %type environment is well-defined if every successful query implies the
% %success of more specific queries. This condition is needed for two
% %reasons. Firstly, dynamic resolution is always performed with all free
% %type variables substituted by concrete types. Thus, type system needs
% %to consider all possible instantiation of the rule type of a
% %query. Secondly, resolution is, in general, not stable under an
% %arbitrary substitution. Without the condition, the type system becomes
% %unsound; i.e dynamic resolution may fail even if static resolution
% %succeeds. Consider following example:
% %%Rule $\TyQuery$ checks whether resolution is success under arbitrary substitution. 
% %%We would like to determine statically (and conservatively) whether a query may
% %%fail at runtime or not. It may seem sufficient for this purpose to
% %%statically mimic the dynamic resolution mechanism of the operational semantics.
% %%Instead of performing this static resolution with actual rule values, we can
% %%base ourselves on the types of the rules in the implicit environment, without
% %%taking into account all possible control flows.
% %%Unfortunately, this naive static resolution for each query does not guarantee
% %%runtime safety. Parametric polymorphism throws a spanner in the works.
% %%Firstly, dynamic resolution is always performed with more specific types,
% %%where free type variables have been substituted by other types. Secondly,
% %%resolution is, in general, not stable under an arbitrary substitution. 
% %% Without considering stability of resolution, these two facts together result 
% %% in an unsound type system where dynamic resolution may fail even if static 
% %% resolution succeeds. 
% %\[
% %  \{\forall \beta.\beta \rightarrow \beta\} ; \{ \{ \tybool \} \To
% %\tyint \rightarrow \tyint\} \vturns a \rightarrow a
% %  \] Statically, this query resolves against the first rule. However,
% %at runtime, if $\alpha$ is instantiated to $\tyint$, the second rule
% %is used, which fires a recursive resolution for $\tybool$. As the
% %environment does not support $\tybool$, dynamic resolution fails. The
% %well-definedness condition rules out this possibility.
% 
% % \paragraph{Distinct Context}
% %Rule $\TyRule$ uses $\nonoverlap$ predicate to avoid overlapping
% %within rule type contexts. $\nonoverlap$ predicate checks whether rule
% %types within contexts can overlap or not. $\overlap$ predicate, used
% %as a component of $\nonoverlap$, checks whether two given rule types
% %can overlap or not. The predicate consider all possible substitutions
% %because instantiating free type variables may introduce
% %overlap. Following example illustrates the case:
% %  \[
% %    \{\forall \beta.\beta \rightarrow \tyint \rightarrow \beta, 
% %      \forall \beta.\alpha \rightarrow \beta \rightarrow \beta\} \vturns
% %    \alpha \rightarrow \alpha \rightarrow \alpha
% %  \]
% %\noindent
% %Statically, there is only one matching rule in the environment (the second
% %one). However, at runtime, $\alpha$ may be instantiated to $\tyint$. Then the two
% %rules overlap and resolution becomes incoherent. We use $\nonoverlap$ within
% %\TyRule{} to prevent such possibility. We only accepts overlap when two
% %types are going to be the same type after substitution.
% 
% %In $\ourlang$, a major reason of runtime errors is a lookup failure during a query
% %esolution. 
% %  As explained in 
% %A runtime environment may have overlap that leads to lookup failure. 
% %Basically, \coherent{}  condition in $\StaRes$ rule excludes lookup failures
% %directly exposible by a type environment and a static query type. 
% %\coherent{} enforces type level lookup success under any substitution. 
% %Both existence of matching rule and absence of overlapping instances at type level 
% %are ensured. 
% %However, a runtime environment may have overlap that is not detectable by consulting
% %with a type environment and a query type. 
% %If different entities in a runtime environment
% %have the same type, they will be coerced into one type at type level reasoning. 
% %Type system is equipped with conditions to prevent such failure in advance.
% %Rule application and resolution may be responsible for
% %introducing overlap that is not visible at query site. 
% 
% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
% % \paragraph{Algorithms}
% % All conditions except \unambiguous{} are checked with type
% % unification; the \unambiguous{} condition can be checked
% % syntactically.
% 
% % \algnotext{EndFor}
% % \algnotext{EndIf}
% % \algnotext{EndProcedure}
% % \algnotext{Procedure}
% % \begin{algorithm}
% % \small
% %   \caption{$\coherent(\env, \type)$}\label{alg:coherent}
% %   \begin{algorithmic}[1]
% %     \Procedure
% %     \State assume $\env = \cdot;\rulesetvar_1;\dots;\rulesetvar_n$
% %     \State $\rulet$ $\gets$ $\lookup{\env}{\type}$
% %     \State $\rulesetvar_i$ $\gets$ the context that has $\rulet$
% %     \ForAll {$j > i$}
% %       \ForAll {$\forall \overline{\alpha}.\rulesetvar \Rightarrow \tau' \in \rulesetvar_j$}
% %         \If {$\unify{\tau}{\tau'}{\overline{\alpha} \cup \ftv{\tau}} \neq {\it error}$}
% %           \State \Return {\it false}
% %         \EndIf
% %       \EndFor 
% %     \EndFor
% %     \ForAll {$\forall \overline{\alpha}.\rulesetvar \Rightarrow \tau' \in 
% %               \rulesetvar_i \setminus \rulet$}
% %       \If {$\unify{\tau}{\tau'}{\overline{\alpha} \cup \ftv{\tau}}\neq {\it error}$}
% %       \State \Return {\it false}
% %       \EndIf  
% %     \EndFor
% %     \State \Return {\it true}
% %     \EndProcedure
% %   \end{algorithmic}
% % \end{algorithm}
% 
% % \begin{itemize}
% % 
% % \item Algorithm~\ref{alg:coherent} checks the
% %   $\coherent(\env, \type)$ condition. It checks if there is no rule
% %   type $\rho' = \rulesch{\alpha}{\rulesetvar}{\type'}$ other than
% %   $\lookup{\env}{\type}$ in the environment such that $\type'$ and
% %   $\type$ are unifiable. To see why this checks the
% %   \coherent{} condition, suppose that there exists $\rulet' =
% %   \rulesch{\alpha}{\rulesetvar}{\type'}$ whose return type $\type'$ is
% %   unifiable with $\type$ and let $\theta$ be the unifier. Then,
% %   according to the following steps, we can show that there exists
% %   $\theta'$ such that $\theta'(\lookup{\env}{\tau}) \neq
% %   \lookup{(\theta'\env)}{\theta' \tau}$: Let $\rho' \neq
% %   \lookup{\env}{\type}$ and $\theta_1\theta_2 = \theta$ such that
% %   $\theta_1$ is a restriction $\theta\mid_{\bar{\alpha}}$ and
% %   $\theta_2$ is the rest $\theta\mid_{\bar{\alpha}}^{-}$ of $\theta$
% %   for non-$\bar{\alpha}$'s. Then, by definitions and $\ftv{\type} \cap
% %   \bar{\alpha} = \nil$, following equivalences holds: {\small
% %   \begin{align}
% %     \theta \type = \theta \type' 
% %     & \eqv\theta_1 \cdot \theta_2 \type' = \theta_1 \cdot \theta_2
% %     \type \\
% %     (1) \eqv~ \theta_1 \cdot \theta_2 \type' = \theta_2
% %     \type &
% %     \eqv~ \theta_2 \rulet' \succ \theta_2 \type \\
% %     (2) \eqv~ \lookup{(\theta_2 \env)}{\theta_2 \type} = \theta_2
% %     \rulet'. \nonumber
% %   \end{align}
% %   }
% %   \indent For example, the algorithm returns false when $\env = |{Int -> Int};
% %   {{Bool} => Int -> a}|$ and $\type = |Int -> Int|$, because the
% %   return type $|Int -> a|$ of rule type $|{Bool} => Int -> a|$ is
% %   unifiable with |Int -> Int|.
% % 
% % \item The $\distinctctx(\rulesetvar)$ condition requires that no two
% %   rule types $\rulet_1$ and $\rulet_2$ in the context $\rulesetvar$
% %   are unifiable. Thus, we check if unification fails for all pairs
% %   of rule types in the context. The $\distinctwith$ condition is done
% %   similarly.
% % 
% % \item The $\disjoint(\rulesetvar_1, \rulesetvar_2)$ condition requires
% %   that no two rule types $\rulet_1 \in \rulesetvar_1$ and $\rulet_2
% %   \in \rulesetvar_2$ are unifiable. Thus, we check if unification
% %   fails for all pairs of rule types in two contexts, one rule type
% %   from each context.
% % 
% % \end{itemize}
% 
% 
% %-------------------------------------------------------------------------------
% % OLD TEXTS
% %
% % omit lemma about semantics typing and closure
% %
% %By applying ${\tt clear}$ to an argument part of a rule application expression
% %at \TyRApp, type system protects rum-time environments from runtime ambiguity.
% %If an applying runtime closure has typing, new environment made of closure contents
% %and an argument rule program always have proper typing. 
% %
% %  Another point to check is query positions because partial resolution can cause problems. 
% %Static resolution reflects the structure of dynamic resolution. Resolution pick one rule
% %from environment, instantiate it, and recursive resolve difference between a queried rule
% %and picked one (partial resolution). Problem here is that partially resolved entities and
% %yet unresolved entities can cause runtime ambiguity.
% %
% %To ensure semantic typing for the runtime result of resolution, static
% %resolution also includes a \disjoint check.
% %As a consequence, if static resolution succeeds, then runtime resolution also
% %succeeds and yields a well typed result. 
% %
% %
% 
% %Rule application sites may also be responsible for introducing overlap that
% %is not visible at query sites.
% %  \[
% %  \ruleapp
% %    {(\ruleabs
% %      {(\{\tyint\} \Rightarrow \tyint)}
% %      {?\tyint})}
% %    {\{\tyint:3, \tyint:6\}}
% %  \] 
% %\noindent
% %Here, rule application introduces overlap in an obvious manner.
% %Instantiation of type variables, may render this situation less obvious.
% %  \[\begin{array}{l}
% %  \ruleabs
% %    {(\forall \alpha.\{\alpha\}\Rightarrow \alpha \times \tyint)}{}\\
% %    \quad 
% %    \ruleapp
% %      {(\ruleabs
% %        {(\{\alpha,\tyint\} \Rightarrow \alpha \times \tyint)}
% %        {(?\alpha, ?\tyint)})}
% %      {\{\alpha:?\alpha, \tyint:6\}}
% %  \end{array}\]
% %\noindent
% %When the above nested rule (and thus $\alpha$) is instantiated to $\tyint$, we end
% %up with two $\tyint$ rules in the environment.
% 
% %\tom{The following lemma only repeats the definition of \texttt{well defined}. Does
% %it have any value?}
% %\begin{lemma}
% %Let $\env$ be a type environment and $\rulet$ be a rule type,
% %and assume ${\tt welldefined}(\env)$.
% %If $\env \vturns \rulet$, then $\forall \theta. \theta(\env) \vturns \theta(\rulet)$.
% %\end{lemma}
% 
% 
% %--------------------------------------------------------------------------------------
% % TOM: DROPPED BECAUSE WE NO LONGER COVER THE OPERATIONAL SEMANTICS
% % \subsection{Type Soundness}
% % 
% % \paragraph{Semantic Typing}
% % 
% % \figtwocol{fig:sem_type}{Semantic Typing}{
% % \small
% % 
% % \bda{lc} 
% % 
% % \multicolumn{2}{l}{\myruleform{\vtyping \relation{v}{\type}}} \\
% % 
% % \TyRClos &
% % \myirule
% % { \rulet \leteq \rulesch{\alpha}{\rulesetvar}{\type} \\
% %   \vtyping \relation{\rulepgmvar}{\rulesetvar'} \quad 
% %   \vtyping \relation{\tstate}{\dom(\tstate)} \\
% %   \dom(\tstate); \rulesetvar' \cup \rulesetvar \turns 
% %   \relation{e}{\type} \\
% %   \shade{\disjoint(\rulesetvar,\rulesetvar')} \quad
% %   \shade{\unambiguous(\rulet)}
% % }
% % { \vtyping 
% %   \relation{\rclos{\rulet, e, \tstate, \rulepgmvar}}{\rulet}
% % } \\ \\
% % 
% % \multicolumn{2}{l}{
% %   \myruleform{\vtyping \relation{\tstate}{\env}}} \\ \\
% % 
% % \TyREnv &
% % \myirule
% % {\vtyping \tstate:\env \quad 
% %   \vtyping \rulepgmvar:\rulesetvar}
% % {\vtyping (\tstate;\rulepgmvar) : (\env;\rulesetvar)} 
% % 
% % \quad\quad
% % \myirule
% % { }
% % { \vtyping \cdot:\cdot }
% % 
% % \\ \\ 
% % 
% % \multicolumn{2}{l}{
% %   \myruleform{\vtyping \relation{\rulepgmvar}{\rulesetvar}}} \\
% % 
% % \TyRPgm &
% % \myirule
% % { \dom(\rulepgmvar) = \rulesetvar \quad \shade{\distinctrs(\rulepgmvar)}\\
% %   \vtyping \relation{v_i}{\rulet_i} \quad
% %   (\forall \relation{\rulet_i}{v_i} \in \rulepgmvar)
% % }
% % { \vtyping \relation{\rulepgmvar}{\rulesetvar}
% % } 
% % 
% % \quad\quad
% % \myirule
% % { }
% % { \vtyping \nil : \nil}
% % % \multicolumn{2}{c}{
% % % \begin{array}{l}
% % %  \unambiguous(\forall \overline{\alpha}.\rulesetvar \Rightarrow \tau) 
% % %  \defeq \overline{\alpha} \subseteq \ftv{\tau} \wedge 
% % %  \forall \rulet_i \in \rulesetvar. \unambiguous(\rulet_i)
% % %  \\
% % %
% % % \end{array}}
% % \eda
% % }
% % 
% % Before proving the soundness of our type system, we first relate
% % values and rule types ($\models \relation{v}{\rulet}$), rule sets
% % and contexts ($\models \relation{\rulepgmvar}{\rulesetvar}$), and
% % environments and type environments ($\models
% % \relation{\tstate}{\env}$) via semantic typing as presented in Figure
% % \ref{fig:sem_type}. If a value, a rule set, or an
% % environment respects semantic typing, we call them {\it well-typed}
% % with respect to the rule type, the context and the type environment,
% % respectively.
% % 
% % We use the $\dom$ function to project a rule set and an
% % environment onto the corresponding context and type environment. Note
% % that $\dom$ is overloaded but clearly distinguishable by the context. For the case
% % of environments, the function preserves the shape of stack. The $\dom$
% % functions are defined as follows:
% % \bda{ll}
% % \dom(\cdot) = \cdot &
% % \dom(\rulepgm) = \ruleset \\
% % \dom(\tstate; \rulepgmvar) = \dom(\tstate); \dom(\rulepgmvar)
% % \eda
% % 
% % % \bruno{Please rephrase more carefully the following sentence. I don't 
% % % understand it.}
% % As the type system imposes several restrictions to prevent runtime
% % ambiguity, well-typed entities (value, rule set and environment)
% % generated by well-typed expressions should also respect those
% % restrictions. Firstly, well-typed values should be typed with
% % unambiguous rule types (\unambiguous). Secondly, there should be no
% % overlap between the partially-resolved context and the rule type
% % context (\disjoint). This is to prevent that no overlap happens when
% % the context of a rule type is discharged by either rule application or
% % further partial resolution. Lastly, well-typed rule sets should not
% % make lookup fail. To ensure this, we use the \distinctrs{} condition
% % whose definition is as follows:
% % \begin{equation*}
% %   \distinctrs(\rulepgmvar) \defeq \forall \relation{\rulet_1}{v_1},
% %   \relation{\rulet_2}{v_2} \in \rulepgmvar. 
% %   \forall \theta. \theta \rulet_1 \neq \theta \rulet_2
% % \end{equation*}
% % \noindent
% % This is exactly the same condition as the one used in \TyRApp{} except we now
% % check that the two given values are distinct.
% % 
% % \paragraph{Type System Properties}
% % We prove the properties of static resolution and typing which
% % are essential for type soundness. 
% % 
% % Firstly, static resolution is stable under type substitution.
% % 
% % \lemresstable{lem:res-stable}
% % 
% % \begin{proof}
% %   By induction on the derivation of static resolution. The proof uses
% %   the fact that all conditions used in \StaRes{} are stable under
% %   substitution.
% % \end{proof}
% % 
% % Using this lemma, we prove that expression typing and semantic typing
% % are also stable under type substitution. 
% % 
% % \lemtystable{lem:ty-stable}
% % 
% % \begin{proof}
% %   By induction on expression typing. For \TyQuery{} case, we use
% %   lemma~\ref{lem:res-stable}.
% % \end{proof}
% % 
% % \lemsemstable{lem:sem-stable}
% % 
% % \begin{proof}
% %   By mutual induction on semantic typing of value, rule set, and
% %   environment. For \TyRClos{} case, we use lemma~\ref{lem:ty-stable}.
% % \end{proof}
% % 
% % \paragraph{Type Soundness}
% % Type soundness is a direct consequence of type preservation of typing
% % rules and static resolution.
% % 
% % \lemrespreserve{lem:res-preserve}
% % \begin{proof}
% %   By induction on the derivation of static resolution.
% % \end{proof}
% % 
% % \lemtypreserve{lem:ty-preserve}
% % \begin{proof}
% %   By simultaneous induction on the derivation of evaluation and
% %   expression typing. For \OpQuery{} case, we use
% %   lemma~\ref{lem:res-preserve}. For \OpInst{} case, we use
% %   lemma~\ref{lem:ty-stable}.
% % \end{proof}
% % 
% % \thmsoundness
% % \begin{proof}
% %   Trivially true by lemma~\ref{lem:ty-preserve}.
% % \end{proof}


%===============================================================================

%-------------------------------------------------------------------------------
\subsection{Termination of Resolution}

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
judgement $\term{\rho}$ defined in Figure~\ref{fig:termination}.

This judgement recursively constrains rule types $\rho_1 \iarrow \rho_2$ to
guarantee that the recursive resolution process is well-founded. In particular,
it defines a size measure $\||\rho\||$ for type terms $\rho$ and makes sure that the size 
of the resolved head type decreases steadily with each recursive resolution
step. 

One potential problem is that the size measure does not properly take into
account universally quantified type variables. It assigns them size 1 but
ignores the fact that the size may increase dramatically when the type variable
is instantiated with a large type. The rule $\TermRule$ makes up for this problem
by requiring a size decrease for all possible instantiations of free type variables.
However, rather than to specify this property non-constructively as 
\[ \forall \bar{\rho}. \||[\bar{\alpha}\mapsto\bar{\rho}]\tau_1\|| < \||[\bar{\alpha}\mapsto\bar{\rho}]\tau_2\|| \]
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
\myruleform{\term{\rho}}
\quad\quad\quad
\TermSimpl \quad
  \myirule{}
          {\term{\tau}} 
\quad\quad\quad
\TermForall \quad
  \myirule{\term{\rho}}
          {\term{\forall \alpha. \rho}} 
\\ \\
\TermRule \quad
  \myirule{\term{\rho_1} \quad\quad \term{\rho_2} \\ 
           \rho_1 \lhd \tau_1 \quad\quad \rho_2 \lhd \tau_2 \quad\quad \tnorm{\tau_1} < \tnorm{\tau_2} \\
           \forall \alpha \in \ftv{\rho_1} \cup \ftv{\rho_2}: \quad \occ{\alpha}{\tau_1} \leq \occ{\alpha}{\tau_2}}  
          {\term{\rho_1 \iarrow \rho_2}} 
\\ \\
\ea
$
    \begin{eqnarray*}
      \occ{\alpha}{\tyint} & = & 0 \\
      \occ{\alpha}{\beta} & = & \left\{ \begin{array}{ll} 
         1 & \hspace{1cm}(\alpha = \beta) \\
         0 & \hspace{1cm}(\alpha \neq \beta)
         \end{array}\right. \\
      \occ{\alpha}{\rho_1 \arrow \rho_2} & = & \occ{\alpha}{\rho_1} + \occ{\alpha}{\rho_2} \\
      \occ{\alpha}{\rho_1 \iarrow \rho_2} & = & \occ{\alpha}{\rho_1} + \occ{\alpha}{\rho_2} \\
      \occ{\alpha}{\forall \beta.\rho} & = & \occ{\alpha}{\rho} \\ \\
      \tnorm{\tyint} & = & 1 \\
      \tnorm{\alpha} & = & 1 \\
      \tnorm{\rho_1 \arrow \rho_2} & = & 1 + \tnorm{\rho_1} + \tnorm{\rho_2} \\
      \tnorm{\rho_1 \iarrow \rho_2} & = & 1 + \tnorm{\rho_1} + \tnorm{\rho_2} \\
      \tnorm{\forall \alpha.\rho} & = & \tnorm{\rho}
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

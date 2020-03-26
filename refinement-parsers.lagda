\documentclass[submission,copyright,creativecommons]{eptcs}

% Uncomment the following line to add the appendix on Context-free grammars:
% \def\includeCFGs{}

\providecommand{\event}{MSFP 2020}

\usepackage[style=numeric,natbib=true]{biblatex}
\addbibresource{handlers.bib}
\setcounter{biburlnumpenalty}{100}

%include agda.fmt
%include refinement-parsers.fmt

%include preamble.tex

%if style == newcode
\begin{code}
open import Prelude

open import Axiom.Extensionality.Propositional
open import Level
postulate extensionality : ∀ {l₁ l₂} -> Extensionality l₁ l₂

_⊆_ : {a : Set} -> (P Q : a -> Set) -> Set
P ⊆ Q = ∀ x -> P x -> Q x
\end{code}
%endif

\begin{document}

\title{Combining predicate transformer semantics for effects:\\a case study in parsing regular languages}
\def\titlerunning{Combining predicate transformer semantics for effects}
\def\authorrunning{Anne Baanen and Wouter Swierstra}
% Of misschien iets als:
% A predicate transformer semantics for parsing
% Verifying parser combinators using predicate transformers
\author{Anne Baanen
  \institute{Vrije Universiteit Amsterdam}
    \and
    Wouter Swierstra
  \institute{Utrecht University}
  }
%\email{\{t.baanen@@vu.nl,w.s.swierstra@@uu.nl\}}}
%
\maketitle              % typeset the header of the contribution

\begin{abstract}
This paper describes how to verify a parser for regular expressions in a functional programming language using predicate transformer semantics for a variety of effects.
%
Where our previous work in this area focused on the semantics for a
single effect, parsing requires a combination of effects:
non-determinism, general recursion and mutable state.  Reasoning about
such combinations of effects is notoriously difficult, yet our
approach using predicate transformers enables the careful separation
of program syntax, correctness proofs and termination proofs.
\end{abstract}

\section{Introduction}
\label{sec:intro}

There is a significant body of work on parsing using combinators
in functional programming langua\-ges~\cite{list-of-successes, hutton, functional-parsers, swierstra-duponcheel, leijen2001parsec, efficient-combinator-parsers, parser-combinators-for-left-recursive, parsing-with-derivatives}, among many others.
Yet how can we ensure that these parsers are correct? There is notably
less work that attempts to  answer this
question~\cite{total-parser-combinators, firsov-certification-context-free-grammars}.

Reasoning about such parser combinators is not at all trivial. They
use a variety of effects: state to store the string being parsed;
non-determinism to handle backtracking; and general recursion to deal
with recursive grammars. Proof techniques, such as equational
reasoning, that are commonly used when reasoning about pure functional programs, are less
suitable when verifying effectful programs~\cite{just-do-it,hutton2008reasoning}.

In this paper, we explore a novel approach, drawing inspiration from recent
work on algebraic effects~\cite{eff, effect-handlers-in-scope,
McBride-totally-free}.  We demonstrate how to reason about all parsers
uniformly using \emph{predicate transformers}~\cite{pt-semantics-for-effects}.
We extend our previous work that uses predicate transformer semantics to reason
about a single effect, to handle the combinations of effects used by parsers.
Our semantics is modular, meaning we can introduce new effects (|Rec| in
Section \ref{sec:combinations}), semantics (|hParser| in Section \ref{sec:dmatch}) and specifications (|terminates-in| in Section \ref{sec:dmatch-correct}) when they are
needed, without having to
rework the previous definitions.  In particular, our careful treatment of
general recursion lets us separate partial correctness
from the proof of termination cleanly. Most existing proofs require combinators to
guarantee that the string being parsed decreases, conflating these two issues.

In particular, the sections of this paper make the following contributions:
\begin{itemize}
\item After quickly revisiting our previous work on predicate
  transformer semantics for effects (Section~\ref{sec:recap}), we show how the
  non-recursive fragment of regular expressions can be correctly
  parsed using non-determinism (Section \ref{sec:regex-nondet}).
\item By combining non-determinism with general recursion (Section \ref{sec:combinations}),
  support for the Kleene star can be added without compromising our previous definitions.
\item Although the resulting parser is not guaranteed to terminate,
  we can define another implementation using Brzozowski derivatives (Section \ref{sec:dmatch}),
  introducing an additional effect and its semantics in the process.
\item Finally, we show that the derivative-based implementation terminates
  and \emph{refines} the original parser (Section \ref{sec:dmatch-correct}).

\ifdefined\includeCFGs
\item Next, we show how this approach may be extended to handle
  context-free languages. To do so, we show how to write parsers using
  algebraic effects (Section \ref{sec:parser}), and map grammars to parsers (Section
  \ref{sec:fromProductions}). Once again, we can cleanly separate the proofs of partial
  correctness (Section \ref{sec:partialCorrectness}) and termination (Section \ref{sec:fromProds-terminates}).
\fi
\end{itemize}

The goal of our work is not so much the verification of a parser for regular languages,
which has been done before~\cite{harper-regex, intrinsic-verification-regex}.
Instead, we aim to illustrate the steps of incrementally developing and verifying a parser
using predicate transformers and algebraic effects.
This work is in the spirit of a Theoretical Pearl~\cite{harper-regex}:
we begin by defining a |match| function that does not terminate. The remainder of the paper
then shows how to fix this function, without having to redo the complete proof of correctness.

All the programs and proofs in this paper are written in the dependently typed language Agda~\cite{agda-thesis}.
The full source code, including lemmas we have chosen to omit for sake of readability,
is available online.\footnote{\url{https://github.com/Vierkantor/refinement-parsers}}
Apart from postulating function extensionality,
we remain entirely within Agda's default theory.

\section{Recap: algebraic effects and predicate transformers}
\label{sec:recap}
Algebraic effects separate the \emph{syntax} and \emph{semantics} of
effectful operations. In this paper, we will model them by taking the
free monad over a given signature~\cite{extensible-effects}, describing certain
operations. Signatures are represented by the type |Sig|, as follows:
\begin{code}
record Sig : Set₁ where
  constructor mkSig
  field
    C : Set
    R : C -> Set
\end{code}
This is Agda syntax for defining a type |Sig| with constructor |mkSig : (C : Set) -> (C -> Set) -> Sig| and two fields, |C : Sig -> Set| and |R : (e : Sig) -> C e -> Set|.
Here the type |C| contains the `commands', or effectful operations
that a given effect supports. For each command |c : C|, the type |R c|
describes the possible responses.
The structure on a signature is that of a \emph{container}~\cite{categories-of-containers}.
The following signature describes two commands: the
non-deterministic choice between two values, |Choice|; and a failure
operator, |Fail|. The response type |RNondet| is defined by pattern matching on the command.
If the command is |Choice|, the response is a |Bool|; the |Fail| command gives no response, indicated by the empty type |⊥|.
\begin{code}
data CNondet : Set where
  Choice  : CNondet
  Fail    : CNondet

RNondet : CNondet -> Set
RNondet Choice  = Bool
RNondet Fail    = ⊥

Nondet = mkSig CNondet RNondet
\end{code}
%if style == newcode
\begin{code}
module NoCombination where
  open Sig
\end{code}
%endif
We represent effectful programs that use a particular effect using the
corresponding \emph{free monad}:
\begin{code}
  data Free (e : Sig) (a : Set) : Set where
    Pure : a -> Free e a
    Op   : (c : C e) -> (R e c -> Free e a) -> Free e a
\end{code}
This gives a monad, with the bind operator defined as follows.
\begin{code}
  _>>=_ : (Forall(a b e)) Free e a -> (a -> Free e b) -> Free e b
  Pure x    >>= f = f x
  Op c k    >>= f = Op c (λ x -> k x >>= f)
\end{code}
%if style == newcode
\begin{code}
  _<$>_ : ∀ {a b e} -> (a → b) → Free e a → Free e b
  f <$> mx = mx >>= λ x → Pure (f x)
\end{code}
%endif
To facilitate programming with effects, we define the following smart
constructors, sometimes referred to as \emph{generic effects} in the
literature~\cite{algebraic-operations-and-generic-effects}:
\begin{code}
  fail : (Forall(a)) Free Nondet a
  fail = Op Fail (λ ())
  choice : (Forall(a)) Free Nondet a -> Free Nondet a -> Free Nondet a
  choice S₁ S₂ = Op Choice (λ b -> if b then S₁ else S₂)
\end{code}
The empty parentheses |()| in the definition of |fail| are Agda syntax for an argument
in an uninhabited type, hence no body for the lambda is provided.

In this paper, we will assign \emph{semantics} to effectful programs
by mapping them to \emph{predicate transformers}.
Each semantics will be computed by a fold over the free monad, mapping
some predicate |P : a -> Set| to a predicate of the entire computation of type |Free (mkSig C R) a -> Set|.
\begin{code}
  wp'' : (implicit(C : Set)) (implicit(R : C -> Set)) (implicit(a : Set)) (alg : (c : C) -> (R c -> Set) -> Set) -> Free (mkSig C R) a -> (a -> Set) -> Set
  (wp alg (Pure x)) P  = P x
  (wp alg (Op c k)) P  = alg c (λ x -> (wp (alg) (k x)) P)
\end{code}
The \emph{predicate transformer} nature of these semantics
becomes evident when we assume the type of responses |R| does not depend on the command |c : C|.
The type of |alg : (c : C) → (R c → Set) → Set| then becomes |C → (R → Set) → Set|,
which is isomorphic to |(R → Set) → (C → Set)|.
Thus, |alg| has the form of a predicate transformer from postconditions of type
|R → Set| into preconditions of type |C → Set|.
% The type of |(wp' alg)| under the same isomorphism becomes
% |(a -> Set) -> (Free e a → Set)|.

Two considerations lead us to define the types as |alg : (c : C) → (R c → Set) → Set|
and |(wp' alg) : Free (mkSig C R) a → (a → Set) → Set|.
By passing the command |c : C| as first argument to |alg|, we allow |R| to depend on |c|.
Moreover, |(wp' alg)| computes semantics,
so it should take a program |S : Free (mkSig C R) a| as its argument
and return the semantics of |S|, which is then of type |(a → Set) → Set|.

In the case of non-determinism, for example, we may want to require that a given
predicate |P| holds for all possible results that may be returned:
%if style == newcode
\begin{code}
module Nondet where
\end{code}
%endif
\begin{code}
  ptAll : (c : CNondet) -> (RNondet c -> Set) -> Set
  ptAll Fail   P  = ⊤
  ptAll Choice P  = P True ∧ P False
\end{code}
A different semantics may instead require that |P| holds on any of the return values:
\begin{code}
  ptAny : (c : CNondet) -> (RNondet c -> Set) -> Set
  ptAny Fail   P  = ⊥
  ptAny Choice P  = P True ∨ P False
\end{code}

%if style == newcode
\begin{code}
module Spec where
\end{code}
%endif

Predicate transformers provide a single semantic domain to relate
programs and specifications~\cite{prog-from-spec}.
Throughout this paper, we will consider specifications consisting of a
pre- and postcondition:
\begin{samepage}
\begin{code}
  record Spec (a : Set) : Set₁ where
    constructor [[_,_]]
    field
      pre : Set
      post : a -> Set
\end{code}
\end{samepage}
Inspired by work on the refinement calculus, we can assign a predicate
transformer semantics to specifications as follows:
\begin{code}
  wpSpec' : (Forall(a)) Spec a -> (a -> Set) -> Set
  wpSpec [[ pre , post ]] P = pre ∧ (∀ o -> post o -> P o)
\end{code}
This computes the `weakest precondition' necessary for a specification
to imply that the desired postcondition |P| holds. In particular, the
precondition |pre| should hold and any possible result satisfying the
postcondition |post| should imply the postcondition |P|.

Finally, we use the \emph{refinement relation} to compare programs and specifications:
\begin{code}
  _⊑_ : (Forall(a : Set)) (pt1 pt2 : (a -> Set) -> Set) -> Set₁
  pt1 ⊑ pt2 = ∀ P -> pt1 P -> pt2 P
\end{code}
Together with the predicate transformer semantics we have defined
above, this refinement relation can be used to relate programs to
their specifications. The refinement relation is both transitive and
reflexive.
%if style == newcode
\begin{code}
  ⊑-refl : (Forall(a)) {pt : (a -> Set) -> Set} -> pt ⊑ pt
  ⊑-refl P x = x
\end{code}
%endif

\section{Regular languages without recursion} \label{sec:regex-nondet}
%if style == newcode
\begin{code}
open import Data.Char using (Char; _≟_)
String = List Char
\end{code}
%endif
To illustrate how to reason about non-deterministic code, we will
define and verify a regular expression matcher. Initially, we will restrict
ourselves to non-recursive regular expressions; we will add recursion
in the next section.

We begin by defining the |Regex| datatype for regular expressions.
An element of this type represents the syntax of a regular expression.
% Introduce formatting for the * operator later, to avoid confusion with multiplication.
%if style == poly
%format _* = "\_\!\mathbin{\star}"
%format * = "\mathbin{\star}"
%endif
\begin{code}
data Regex : Set where
  Empty      : Regex
  Epsilon    : Regex
  Singleton  : Char -> Regex
  _∣_        : Regex -> Regex -> Regex
  _·_        : Regex -> Regex -> Regex
  _*         : Regex -> Regex
\end{code}
The |Empty| regular expression corresponds to the empty
language, while the |Epsilon| expression only matches the empty
string. Furthermore, our language for regular expressions is closed
under choice (|_∣_|), concatenation (|_·_|) and linear repetition
denoted by the Kleene star (|_*|).

The input to the regular expression matcher will be a |String| together with a |Regex| denoting the language to match the string against.
What should our matcher return?  A Boolean value is
not particularly informative; yet we also choose not to provide an
intrinsically correct definition, instead performing extrinsic
verification using our predicate transformer semantics. The |tree|
data type below captures a potential parse tree associated with a
given regular expression:
\begin{code}
tree : Regex -> Set
tree Empty          = ⊥
tree Epsilon        = ⊤
tree (Singleton _)  = Char
tree (l ∣ r)        = Either (tree l) (tree r)
tree (l · r)        = Pair (tree l) (tree r)
tree (r *)          = List (tree r)
\end{code}
In the remainder of this section, we will develop a regular expression
matcher with the following type:
\begin{spec}
  match : (r : Regex) (xs : String) -> Free Nondet (tree r)
\end{spec}
Before we do so, however, we will complete our specification. Although
the type above guarantees that we return a parse tree matching the
regular expression |r|, there is no relation between the tree and the
input string. To capture this relation, we define the following
|Match| data type. A value of type |Match r xs t| states that the
string |xs| is in the language given by the regular expression |r| as
witnessed by the parse tree |t|:

\begin{code}
data Match : (r : Regex) -> String -> tree r -> Set where
  Epsilon     :                                                                                                      Match Epsilon Nil tt
  Singleton   : (implicit(x : Char))                                                                                 Match (Singleton x) (x :: Nil) x
  OrLeft      : (implicit(l r : Regex)) (implicit(xs : String)) (implicit(x : tree l))                               Match l xs x -> Match (l ∣ r) xs (Inl x)
  OrRight     : (implicit(l r : Regex)) (implicit(xs : String)) (implicit(x : tree r))                               Match r xs x -> Match (l ∣ r) xs (Inr x)
  Concat      : (implicit(l r : Regex)) (implicit(ys zs : String)) (implicit(y : tree l)) (implicit(z : tree r))     Match l ys y -> Match r zs z -> Match (l · r) (ys ++ zs) (y , z)
  StarNil     : (implicit(r : Regex))                                                                                Match (r *) Nil Nil
  StarConcat  : (implicit(r : Regex)) (implicit(xs : String)) (implicit(y : tree r)) (implicit(ys : List (tree r)))  Match (r · (r *)) xs (y , ys) -> Match (r *) xs (y :: ys)
\end{code}
Note that there is no constructor for |Match Empty xs ms| for any |xs|
or |ms|, as there is no way to match the |Empty| language with a
string |xs|.  Similarly, the only constructor for |Match Epsilon xs
ms| is where |xs| is the empty string |Nil|. There are two
constructors that produce a |Match| for a regular expression of the
form |l ∣ r|, corresponding to the choice of matching either |l| or
|r|.

The cases for concatenation and iteration are more
interesting. Crucially the |Concat| constructor constructs a match on
the concatenation of the strings |ys| and |zs| -- although there may
be many possible ways to decompose a string into two
substrings. Finally, the two constructors for the Kleene star, |r *|,
match zero (|StarNil|) or many (|StarConcat|) repetitions of |r|.

We will now turn our attention to the |match| function. The complete
definition, by induction on the argument regular expression, can be
found in Figure~\ref{fig:match}. Most of the cases are
straightforward---the most difficult case is that for concatenation,
where we non-deterministically consider all possible splittings of the
input string |xs| into a pair of strings |ys| and |zs|. The
|allSplits| function, defined below, computes all possible splittings:

%if style == newcode
\begin{code}
module AlmostRegex where
  open NoCombination
  open Nondet
  open Spec
\end{code}
%endif
\begin{code}
  allSplits : (Forall(a)) (xs : List a) -> Free Nondet (List a × List a)
  allSplits Nil = Pure (Nil , Nil)
  allSplits (x :: xs) = choice
    (Pure (Nil , (x :: xs)))
    (allSplits xs >>= λ {(ys , zs) → Pure ((x :: ys) , zs)})
\end{code}
\begin{figure}
\begin{code}
  match : (r : Regex) (xs : String) -> Free Nondet (tree r)
  match Empty          xs             = fail
  match Epsilon        Nil            = Pure tt
  match Epsilon        (_ :: _)       = fail
  match (Singleton c)  Nil            = fail
  match (Singleton c)  (x :: Nil)     with c ≟ x
  match (Singleton c)  (c :: Nil)     | yes refl  = Pure c
  match (Singleton c)  (x :: Nil)     | no ¬p     = fail
  match (Singleton c)  (_ :: _ :: _)  = fail
  match (l ∣ r)        xs             = choice (Inl <$> match l xs) (Inr <$> match r xs)
  match (l · r)        xs             = do  (ys , zs) <- allSplits xs
                                            y <- match l ys
                                            z <- match r zs
                                            Pure (y , z)
  match (r *) xs                      = fail
  \end{code}
  \caption{The definition of the |match| function}
  \label{fig:match}
\end{figure}

Finally, we cannot yet implement the case for the Kleene star.  We could
attempt to mimic the case for concatenation, attempting to match |r · (r *)|.
This definition, however, is rejected by Agda as it is not structurally
recursive. For now we choose to simply fail on all such regular expressions.
In Section \ref{sec:combinations} we will fix this issue, after introducing
the auxiliary definitions.

Still, we can prove that the |match| function behaves correctly on all
regular expressions that do not contain iteration. We introduce a |hasNo*|
predicate, which holds of all such iteration-free regular expressions:
\begin{code}
  hasNo* : Regex -> Set
\end{code}
%if style == newcode
\begin{code}
  hasNo* Empty = ⊤
  hasNo* Epsilon = ⊤
  hasNo* (Singleton x) = ⊤
  hasNo* (l · r) = hasNo* l ∧ hasNo* r
  hasNo* (l ∣ r) = hasNo* l ∧ hasNo* r
  hasNo* (r *) = ⊥
\end{code}
%endif
To verify our matcher is correct, we need to prove that it satisfies
the specification consisting of the following pre- and postcondition:
\begin{code}
  pre : (r : Regex) (xs : String) -> Set
  pre r xs = hasNo* r
  post : (r : Regex) (xs : String) -> tree r -> Set
  post = Match
\end{code}
The main correctness result can now be formulated as follows:
\begin{code}
  matchSound : ∀ r xs -> (wpSpec [[ (pre r xs) , (post r xs) ]]) ⊑ (wp ptAll (match r xs))
\end{code}
This lemma guarantees that all the parse trees computed by the |match|
function satisfy the |Match| relation, provided the input regular
expression does not contain iteration. The proof goes by induction on the
regular expression |r|. Although we have omitted the proof, we will sketch the
key lemmas and definitions that are necessary to complete it.

In most of the cases for |r|, the definition of |match r| is uncomplicated and
the proof is similarly simple. As soon as we need to reason about programs
composed using the monadic bind operator, we quickly run into issues. In
particular, when verifying the case for |l · r|, we would like to use
our induction hypotheses on two recursive calls. To do so, we prove the
following lemma that allows us to replace the semantics of a composite
program built using the monadic bind operation with the composition of
the underlying predicate transformers:
\begin{code}
  consequence : (Forall(a b es P)) ∀ pt (mx : Free es a) (f : a -> Free es b) ->
    (wp pt mx) (λ x -> (wp pt (f x)) P) == (wp pt (mx >>= f)) P
\end{code}
%if style == newcode
\begin{code}
  consequence pt (Pure x) f = refl
  consequence pt (Op c k) f = cong (pt c)
    (extensionality λ x -> consequence pt (k x) f)
\end{code}
%endif
Substituting along this equality gives us the lemmas we need to deal with the |_>>=_| operator:
\begin{code}
  wpToBind : (Forall (a b es pt P)) (mx : Free es a) (f : a -> Free es b) ->
    (wp pt mx) (λ x -> (wp pt (f x)) P) -> (wp pt (mx >>= f)) P
  wpFromBind : (Forall (a b es pt P)) (mx : Free es a) (f : a -> Free es b) ->
    (wp pt (mx >>= f)) P -> (wp pt mx) (λ x -> (wp pt (f x)) P)
\end{code}
%if style == newcode
\begin{code}
  wpToBind (hidden(pt = pt)) mx f H = subst id (consequence pt mx f) H
  wpFromBind (hidden(pt = pt)) mx f H = subst id (sym (consequence pt mx f)) H
\end{code}
%endif

Not only does |match (l · r)| result in two recursive calls,
it also makes a call to a helper function |allSplits|.
Thus, we also need to formulate and prove the correctness of that function, as follows:
\begin{code}
  allSplitsPost : String → String × String → Set
  allSplitsPost xs (ys , zs) = xs == ys ++ zs
  allSplitsSound : ∀ xs -> (wpSpec [[ ⊤ , (allSplitsPost xs) ]]) ⊑ (wp ptAll (allSplits xs))
\end{code}
Using |wpToBind|, we can incorporate the correctness proof of |allSplits|
in the correctness proof of |match|.
We refer to the accompanying code for the complete details of these
proofs.
%if style == newcode
\begin{code}
  allSplitsSound Nil        P (preH , postH) = postH _ refl
  allSplitsSound (x :: xs)  P (preH , postH) = postH _ refl ,
    wpToBind (allSplits xs) _ (allSplitsSound xs _ (tt ,
      λ _ H → postH _ (cong (x ::_) H)))

  matchSound Empty xs           P (preH , postH) = tt
  matchSound Epsilon Nil        P (preH , postH) = postH _ Epsilon
  matchSound Epsilon (x :: xs)  P (preH , postH) = tt
  matchSound (Singleton x) Nil P (preH , postH) = tt
  matchSound (Singleton x) (c :: Nil) P (preH , postH) with x ≟ c
  ... | yes refl = postH _ Singleton
  ... | no ¬p = tt
  matchSound (Singleton x) (_ :: _ :: _) P (preH , postH) = tt
  matchSound (l · r) xs P ((preL , preR) , postH) =
    wpToBind (allSplits xs) _ (allSplitsSound xs _ (tt ,
    λ {(ys , zs) splitH → wpToBind (match l ys) _ (matchSound l ys _ (preL ,
    λ y lH → wpToBind (match r zs) _ ((matchSound r zs _ (preR ,
    λ z rH → postH (y , z) (subst (λ xs → Match _ xs _) (sym splitH)
    (Concat lH rH)))))))}))
  matchSound (l ∣ r) xs P ((preL , preR) , postH) =
    wpToBind (match l xs) _ (matchSound l xs _ (preL ,
      λ _ lH → postH _ (OrLeft lH))) ,
    wpToBind (match r xs) _ (matchSound r xs _ (preR ,
      λ _ rH → postH _ (OrRight rH)))
  matchSound (r *) xs P (() , postH)
\end{code}
%endif


\section{General recursion and non-determinism} \label{sec:combinations}
The matcher we have defined in the previous section is incomplete,
since it fails to handle regular expressions that use the Kleene star.
The fundamental issue is that the Kleene star allows for arbitrarily many matches in certain cases, that
in turn, leads to problems with Agda's termination checker.
For example, matching |Epsilon *| with the empty string |""| may unfold the Kleene star infinitely often
without ever terminating.
As a result, we cannot implement |match| for the Kleene star using recursion directly.

Instead, we will deal with this (possibly unbounded) recursion by introducing a new \emph{effect}.
We will represent a recursively defined dependent function of type |(i : I) -> O i|
as an element of the type |(i : I) -> Free (Rec I O) (O i)|.
Here |Rec I O| is a synonym of the the signature type we saw previously~\cite{McBride-totally-free}:
\begin{code}
Rec : (I : Set) (O : I -> Set) -> Sig
Rec I O = mkSig I O
\end{code}
Intuitively, you may want to think of values of type |(i : I) -> Free (Rec I O)
(O i)| as computing a (finite) call graph for every input |i : I|. Instead of
recurring directly, the `effects' that this signature supports require an input
|i : I| corresponding to the argument of the recursive call; the continuation
abstracts over a value of type |O i|, corresponding to the result of a
recursive call. Note that the functions defined in this style are \emph{not}
recursive; instead we will need to write handlers to unfold the function
definition or prove termination separately. A handler for the |Rec| effect,
under the intended semantics, thus behaves like a fixed-point combinator,
introducing recursion to an otherwise recursion-free language by
substituting the function body in each recursive call.

We cannot, however, define a |match| function of the form |Free (Rec _
_)| directly, as our previous definition also used non-determinism. To
account for both non-determinism and unbounded recursion, we need a
way to combine effects. Fortunately, free monads are known to be
closed under coproducts; there is a substantial body of work that
exploits this to (syntactically) compose separate
effects~\cite{effect-handlers-in-scope, la-carte}.

% We can combine two effects in a straightforward way: given signatures |mkSig C₁ R₁| and |mkSig C₂ R₂|,
% we can define a combined signature by taking the disjoint union of the commands and responses,
% resulting in |mkSig (Either C₁ C₂) [ R₁ , R₂ ]|,
% where |[ R₁ , R₂ ]| is the unique map given by applying |R₁| to values in |C₁| and |R₂| on |C₂|~\cite{effect-handlers-in-scope}.
% If we want to support more effects, we can repeat this process of disjoint unions,
% but this quickly becomes somewhat cumbersome.
% For example, the disjoint union construction is associative semantically, but not syntactically.
% If two programs have the same set of effects that is associated differently, we cannot directly compose them.

Rather than restrict ourselves to the binary composition using
coproducts, we modify the |Free| monad to take a \emph{list} of
signatures as its argument, taking the coproduct of the elements of
the list as its signature functor.  The |Pure| constructor remains
unchanged, while the |Op| constructor additionally takes an index into the
list to specify the effect that is invoked.
%if style == newcode
\begin{code}
module Combinations where
  open Sig
  open AlmostRegex using (allSplitsPost)
\end{code}
%endif
\begin{code}
  data Free (es : List Sig) (a : Set) : Set₁ where
    Pure : a -> Free es a
    Op : (hidden(e : Sig)) (i : e ∈ es) (c : C e) (k : R e c -> Free es a) -> Free es a
\end{code}
By using a list of effects instead of allowing arbitrary disjoint unions,
we have effectively chosen that the disjoint unions canonically associate to the right.
% Since the disjoint union is also commutative,
% it would be cleaner to have the collection of effects be unordered as well.
% Unfortunately, working with such multisets in Agda is  type that is easy to work with.
We choose to use the same names and (almost) the same syntax for this new definition of |Free|,
since all the definitions that we have seen previously can be readily adapted to work with this data type instead.
%if style == newcode
\begin{code}
  _>>=_ : ∀ {a b es} -> Free es a -> (a -> Free es b) -> Free es b
  Pure x >>= f = f x
  Op i c k >>= f = Op i c λ x -> k x >>= f
  _>>_ : ∀ {a b es} → Free es a → Free es b → Free es b
  mx >> my = mx >>= const my
  >>=-assoc : ∀ {a b c es} (S : Free es a) (f : a -> Free es b) (g : b -> Free es c) ->
    (S >>= f) >>= g == S >>= (λ x -> f x >>= g)
  >>=-assoc (Pure x) f g = refl
  >>=-assoc (Op i c k) f g = cong (Op i c) (extensionality λ x -> >>=-assoc (k x) _ _)
  >>=-Pure : ∀ {a es} (S : Free es a) ->
    S >>= Pure == S
  >>=-Pure (Pure x) = refl
  >>=-Pure (Op i c k) = cong (Op i c) (extensionality λ x -> >>=-Pure (k x))
  _<$>_ : ∀ {a b es} -> (a → b) → Free es a → Free es b
  f <$> mx = mx >>= λ x → Pure (f x)
\end{code}
%endif

Most of this bookkeeping involved with different effects can be inferred using Agda's \emph{instance arguments}~\cite{instance-arguments-agda}.
Instance arguments, marked using the double curly braces |⦃ ^^ ⦄|, are
automatically filled in by Agda, provided a unique value of the
required type can be found. For example, we can define the generic
effects that we saw previously as follows:
\begin{code}
  fail : (Forall(a es)) ⦃ iND : Nondet ∈ es ⦄ -> Free es a
  fail ⦃ iND ⦄ = Op iND Fail (λ ())
  choice : (Forall(a es)) ⦃ iND : Nondet ∈ es ⦄ -> Free es a -> Free es a -> Free es a
  choice ⦃ iND ⦄ S₁ S₂ = Op iND Choice (λ b -> if b then S₁ else S₂)

  call : (Forall(I O es)) ⦃ iRec : Rec I O ∈ es ⦄ -> (i : I) -> Free es (O i)
  call ⦃ iRec ⦄ i = Op iRec i Pure
\end{code}
These now operate over any free monad with effects given by |es|,
provided we can show that the list |es| contains the |Nondet| and
|Rec| effects respectively.
%if style == newcode
\begin{code}
  choices : ∀ {es a} ⦃ iND : Nondet ∈ es ⦄ → List (Free es a) → Free es a
  choices ⦃ iND ⦄ = foldr choice fail
\end{code}
%endif
For convenience of notation, we introduce the |(RecArr _ es _)| notation for the type of generally recursive functions with effects in |es|,
i.e. Kleisli arrows into |Free (Rec _ _ :: es)|.
\begin{code}
  RecArr' : (I : Set) (es : List Sig) (O : I → Set) → Set₁
  (RecArr I es O) = (i : I) -> Free (Rec I O :: es) (O i)
\end{code}
%if style == newcode
\begin{code}
instance
  inHead : ∀ {l} {a : Set l} {x : a} {xs : List a} → x ∈ (x :: xs)
  inHead = ∈Head
  inTail : ∀ {l} {a : Set l} {x x' : a} {xs : List a} → ⦃ i : x ∈ xs ⦄ → x ∈ (x' :: xs)
  inTail ⦃ i ⦄ = ∈Tail i
\end{code}
%endif

With the syntax for combinations of effects defined, let us turn to semantics.
Since the weakest precondition predicate transformer for a single effect is given as a fold
over the effect's signature,
the semantics for a combination of effects can be given by a list of such semantics.
%if style == newcode
\begin{code}
module Stateless where
  open Combinations
  open Sig
  open Spec
  open AlmostRegex using (allSplitsPost)
\end{code}
%endif
\begin{code}
  record PT (e : Sig) : Set₁ where
    constructor mkPT
    field
      pt    : (c : C e) → (R e c → Set) → Set
      mono  : ∀ c P P' → (∀ x -> P x -> P' x) → pt c P → pt c P'
\end{code}
\begin{samepage}
\begin{code}
  data PTs : List Sig -> Set₁ where
    Nil   : PTs Nil
    _::_  : (Forall(e es)) PT e -> PTs es -> PTs (e :: es)
\end{code}
\end{samepage}
The record type |PT| not only contains a predicate transformer |pt|,
but also a proof that this predicate transformer is
\emph{monotone}. Several lemmas throughout this paper, such as the
|terminates-fmap| lemma of Section~\ref{sec:dmatch-correct}, rely on the monotonicity of the
underlying predicate transformers;
for each semantics we present, the proof of monotonicity is immediate.

Given such a list of predicate transformers,
defining the semantics of an effectful program is a straightforward generalization of the previously defined semantics.
The |Pure| case is identical, and in the |Op| case we can apply the predicate transformer returned by the |lookupPT| helper function.
\begin{code}
  lookupPT : (Forall(C R es)) (pts : PTs es) (i : mkSig C R ∈ es) -> (c : C) -> (R c -> Set) -> Set
  lookupPT (pt :: pts)  ∈Head      = PT.pt pt
  lookupPT (pt :: pts)  (∈Tail i)  = lookupPT pts i
\end{code}
%if style == newcode
\begin{code}
  lookupMono : ∀ {C R es} (pts : PTs es) (i : mkSig C R ∈ es) -> ∀ c P P' → P ⊆ P' → lookupPT pts i c P → lookupPT pts i c P'
  lookupMono (pt :: pts) ∈Head      = PT.mono pt
  lookupMono (pt :: pts) (∈Tail i)  = lookupMono pts i
\end{code}
%endif
This results in the following definition of the semantics for combinations of effects.
\begin{code}
  wp'' : (Forall(a es)) (pts : PTs es) -> Free es a -> (a -> Set) -> Set
  (wp pts (Pure x))    P  = P x
  (wp pts (Op i c k))  P  = lookupPT pts i c (λ x -> (wp pts (k x)) P)
\end{code}

The effects that we will use for our |match| function consist of a
combination of non-determinism and general recursion.  Although we can
reuse the |ptAll| semantics of non-determinism, we have not yet given
the semantics for recursion.  However, it is not as easy to give a
predicate transformer semantics for recursion in general, since the
intended semantics of a recursive call depend on the function that is
being defined. Instead, to give semantics to a recursive function, we
assume that we have been provided with a relation of the type |(i : I)
-> O i -> Set|, reminiscent of a loop invariant in an imperative
program. The semantics then establishes whether or not the recursive
function adheres to this invariant or not:
\begin{code}
  ptRec : (Forall(I O)) ((i : I) -> O i -> Set) -> PT (Rec I O)
  PT.pt    (ptRec R) i P                 = ∀ o -> R i o -> P o
\end{code}
%if style == newcode
\begin{code}
  PT.mono  (ptRec R) c P P' imp asm o h  = imp _ (asm _ h)
\end{code}
%endif
As we shall see shortly, when revisiting the |match| function, the
|Match| relation defined previously will fulfill the role of this
`invariant.'

% In the case of verifying the |match| function, the |Match| relation will play the role of |R|.
% If we use |ptRec R| as a predicate transformer to check that a recursive function satisfies the relation |R|,
% then we are proving \emph{partial correctness}, since we assume each recursive call successfully returns
% a correct value according to the relation |R|.

To deal with the Kleene star, we rewrite |match| as a generally recursive function using a combination of effects.
Since |match| makes use of |allSplits|, we also rewrite that function to use a combination of effects.
The types become:
\begin{code}
  allSplits : (Forall(a es)) ⦃ iND :  Nondet ∈ es ⦄ -> List a -> Free es (List a × List a)
  match : (Forall(es)) ⦃ iND : Nondet ∈ es ⦄ → (RecArrBinding (x) (Regex × String) es (tree (Pair.fst x)))
\end{code}

%if style == newcode
\begin{code}
  allSplits Nil = Pure (Nil , Nil)
  allSplits (x :: xs) = choice
    (Pure (Nil , (x :: xs)))
    (allSplits xs >>= λ {(ys , zs) → Pure ((x :: ys) , zs)})

  match (Empty , xs) = fail
  match (Epsilon , Nil) = Pure tt
  match (Epsilon , xs@(_ :: _)) = fail
  match ((Singleton c) , Nil) = fail
  match ((Singleton c) , (x :: Nil)) with c ≟ x
  match ((Singleton c) , (.c :: Nil)) | yes refl = Pure c
  match ((Singleton c) , (x :: Nil)) | no ¬p = fail
  match ((Singleton c) , (_ :: _ :: _)) = fail
  match ((l · r) , xs) = do
    (ys , zs) <- allSplits xs
    y <- call (hiddenInstance(∈Head)) (l , ys)
    z <- call (hiddenInstance(∈Head)) (r , zs)
    Pure (y , z)
  match ((l ∣ r) , xs) = choice
    (Inl <$> call (hiddenInstance(∈Head)) (l , xs))
    (Inr <$> call (hiddenInstance(∈Head)) (r , xs))
\end{code}
%endif
Since the index argument to the smart constructor is inferred by Agda,
the only change in the definition of |match| and |allSplits| will be
that |match| now does have a meaningful branch for the Kleene star case:
\begin{samepage}
\begin{code}
  match ((r *) , Nil) = Pure Nil
  match ((r *) , xs@(_ :: _)) = do
    (y , ys) <- call (hiddenInstance(∈Head)) ((r · (r *)) , xs)
    Pure (y :: ys)
\end{code}
\end{samepage}

The effects we need to use for running |match| are a combination of non-determinism and general recursion.
As discussed, we first need to give the specification for |match| before we can verify a program that performs a recursive |call| to |match|.
%if style == newcode
\begin{code}
  ptAll : PT Nondet
  PT.pt ptAll Fail P = ⊤
  PT.pt ptAll Choice P = P True ∧ P False
  PT.mono ptAll Fail P P' imp asm = asm
  PT.mono ptAll Choice P P' imp (fst , snd) = imp _ fst , imp _ snd
  ptAny : PT Nondet
  PT.pt ptAny Fail P = ⊥
  PT.pt ptAny Choice P = P True ∨ P False
  PT.mono ptAny Fail P P' imp asm = asm
  PT.mono ptAny Choice P P' imp (Inl asm) = Inl (imp _ asm)
  PT.mono ptAny Choice P P' imp (Inr asm) = Inr (imp _ asm)
\end{code}
%endif
\begin{code}
  matchSpec : (r,xs : Pair Regex String) -> tree (Pair.fst r,xs) -> Set
  matchSpec (r , xs) ms = Match r xs ms

  wpMatch' : (Forall(a)) Free (Rec (Pair Regex String) (tree ∘ Pair.fst) :: Nondet :: Nil) a ->
    (a -> Set) -> Set
  wpMatch S = (wp (ptRec matchSpec :: ptAll :: Nil) S)
\end{code}

%if style == newcode
\begin{code}
  consequence : ∀ {a b es P} pts (mx : Free es a) (f : a -> Free es b) ->
    wp pts mx (λ x -> wp pts (f x) P) == wp pts (mx >>= f) P
  consequence pts (Pure x) f = refl
  consequence pts (Op i c k) f = cong (lookupPT pts i c) (extensionality λ x -> consequence pts (k x) f)

  wpToBind : ∀ {a b es pts P} (mx : Free es a) (f : a -> Free es b) ->
    wp pts mx (λ x -> wp pts (f x) P) -> wp pts (mx >>= f) P
  wpToBind {pts = pts} mx f H = subst id (consequence pts mx f) H

  wpFromBind : ∀ {a b es pts P} (mx : Free es a) (f : a -> Free es b) ->
    wp pts (mx >>= f) P -> wp pts mx (λ x -> wp pts (f x) P)
  wpFromBind {pts = pts} mx f H = subst id (sym (consequence pts mx f)) H
\end{code}
%endif

We can reuse exactly our proof that |allSplits| is correct,
since we use the same semantics for the non-determinism used in the definition of |allSplits|.
Similarly, the partial correctness proof of |match| will be the same on all cases except the Kleene star.
%if style == newcode
\begin{code}
  allSplitsSound : ∀ (xs : String) ->
    (wpSpec [[ ⊤ , (λ {(ys , zs) → xs == ys ++ zs})]]) ⊑ (wpMatch (allSplits (hiddenInstance(∈Tail ∈Head)) xs))
  allSplitsSound Nil        P (fst , snd) = snd _ refl
  allSplitsSound (x :: xs)  P (fst , snd) = snd _ refl ,
    wpToBind (allSplits xs) _ (allSplitsSound xs _ (tt , λ {(ys , zs) H → snd _ (cong (x ::_) H)}))
\end{code}
On the other hand, the correctness proof for |match| needs a bit of tweaking to deal with the difference in the recursive steps.
\begin{code}
  matchSound : ∀ r,xs -> (wpSpec [[ ⊤ , matchSpec r,xs ]]) ⊑ wpMatch (match (hiddenInstance(∈Head)) r,xs)
  matchSound (Empty , xs) P (preH , postH) = tt
  matchSound (Epsilon , Nil)       P (preH , postH) = postH _ Epsilon
  matchSound (Epsilon , (_ :: _))  P (preH , postH) = tt
  matchSound (Singleton c , Nil)            P (preH , postH) = tt
  matchSound (Singleton c , (x :: Nil))     P (preH , postH) with c ≟ x
  matchSound (Singleton c , (.c :: Nil))    P (preH , postH) | yes refl = postH _ Singleton
  matchSound (Singleton c , (x :: Nil))     P (preH , postH) | no ¬p = tt
  matchSound (Singleton c , (_ :: _ :: _))  P (preH , postH) = tt
  matchSound ((l · r) , xs) P (preH , postH) = wpToBind (allSplits xs) _
    (allSplitsSound xs _ (_ , (λ {(ys , zs) splitH y lH z rH → postH (y , z)
    (coerce (cong (λ xs → Match _ xs _) (sym splitH)) (Concat lH rH))})))
  matchSound ((l ∣ r) , xs) P (preH , postH) =
    (λ o H -> postH _ (OrLeft H)) ,
    (λ o H -> postH _ (OrRight H))
\end{code}
%endif
Now we are able to prove correctness of |match| on a Kleene star.
\begin{code}
  matchSound ((r *) , Nil)        P (preH , postH)      = postH _ StarNil
  matchSound ((r *) , (x :: xs))  P (preH , postH) o H  = postH _ (StarConcat H)
\end{code}

At this point, we have defined a matcher for regular languages and
formally proven that when it succeeds in recognizing a given string,
this string is indeed in the language generated by the argument
regular expression.  However, the |match| function does not
necessarily terminate: if |r| is a regular expression that accepts the
empty string, then calling |match| on |r *| and a string |xs| will
diverge. In the next section, we will write a new parser that is guaranteed to
terminate and show that this parser refines the |match| function
defined above.

\section{Derivatives and handlers} \label{sec:dmatch}
Since recursion on the structure of a regular expression does not guarantee
termination of the parser, we can instead perform recursion on the string to be
parsed, changing the regular expression to be matched based on the characters
we have seen.

The \emph{Brzozowski derivative} of a formal language |L| with respect to a character |x| consists of all strings |xs| such that |x :: xs ∈ L|~\cite{Brzozowski}.
Crucially, if |L| is regular, so are all its derivatives.
Thus, let |r| be a regular expression, and |d r /d x| an expression for the derivative with respect to |x|,
then |r| matches a string |x :: xs| if and only if |d r /d x| matches |xs|.
This suggests the following implementation of matching an expression |r| with a string |xs|:
if |xs| is empty, check whether |r| matches the empty string;
otherwise remove the head |x| of the string and try to match |d r /d x|.

The first step in implementing a parser using the Brzozowski derivative is to compute the derivative for a given regular expression.
Following \citet{Brzozowski}, we use a helper function |matchEpsilon| that decides whether an expression matches the empty string.
\begin{code}
  matchEpsilon : (r : Regex) -> Dec (Sigma (tree r) (Match r Nil))
\end{code}
%if style == newcode
\begin{code}
  nilConcat : (Forall(l r xs x,y)) Match (l · r) xs x,y -> xs == Nil -> Pair (Sigma (tree l) (Match l Nil)) (Sigma (tree r) (Match r Nil))
  nilConcat (Concat {ys = Nil} {Nil} y z) cat = (_ , y) , (_ , z)
  nilConcat (Concat {ys = Nil} {x :: zs} ml mr) ()
  nilConcat (Concat {ys = x :: ys} {zs} ml mr) ()

  matchEpsilon Empty = no (λ ())
  matchEpsilon Epsilon = yes (tt , Epsilon)
  matchEpsilon (Singleton x) = no (λ ())
  matchEpsilon (l · r) with matchEpsilon l | matchEpsilon r
  matchEpsilon (l · r) | yes (ml , pl) | yes (mr , pr) = yes ((ml , mr) , (Concat pl pr))
  matchEpsilon (l · r) | yes pl | no ¬pr = no λ {(m , x) -> ¬pr (Pair.snd (nilConcat x refl))}
  matchEpsilon (l · r) | no ¬pl | yes pr = no λ {(m , x) -> ¬pl (Pair.fst (nilConcat x refl))}
  matchEpsilon (l · r) | no ¬pl | no ¬pr = no λ {(m , x) -> ¬pl (Pair.fst (nilConcat x refl))}
  matchEpsilon (l ∣ r) with matchEpsilon l | matchEpsilon r
  matchEpsilon (l ∣ r) | yes (ml , pl) | yes pr = yes (Inl ml , OrLeft pl)
  matchEpsilon (l ∣ r) | yes (ml , pl) | no ¬pr = yes (Inl ml , OrLeft pl)
  matchEpsilon (l ∣ r) | no ¬pl | yes (mr , pr) = yes (Inr mr , OrRight pr)
  matchEpsilon (l ∣ r) | no ¬pl | no ¬pr = no λ {(Inl ml , OrLeft pl) -> ¬pl (ml , pl) ; (Inr mr , OrRight pr) -> ¬pr (mr , pr)}
  matchEpsilon (r *) = yes (Nil , StarNil)
\end{code}
%endif
The definition of |matchEpsilon| is given by structural recursion on the regular expression, just as the derivative operator is:
\begin{samepage}
\begin{code}
  d_/d_ : Regex -> Char -> Regex
  d Empty        /d c    = Empty
  d Epsilon      /d c    = Empty
  d Singleton x  /d c    with c ≟ x
  ...                    | yes p  = Epsilon
  ...                    | no ¬p  = Empty
  d l · r        /d c    with matchEpsilon l
  ...                    | yes p  = ((d l /d c) · r) ∣ (d r /d c)
  ...                    | no ¬p  = (d l /d c) · r
  d l ∣ r        /d c    = (d l /d c) ∣ (d r /d c)
  d r *          /d c    = (d r /d c) · (r *)
\end{code}
\end{samepage}

To use the derivative of |r| to compute a parse tree for |r|,
we need to be able to convert a tree for |d r /d x| to a tree for |r|.
As this function `inverts' the result of differentiation, we name it |integralTree|:
\begin{code}
  integralTree : (implicit(x : Char)) (r : Regex) -> tree (d r /d x) → tree r
\end{code}
Its definition closely follows the pattern matching performed in the definition of |d_/d_|.
%if style == newcode
\begin{code}
  integralTree Empty ()
  integralTree Epsilon ()
  integralTree (Singleton x) t = x
  integralTree (l ∣ r) (Inl x) = Inl (integralTree l x)
  integralTree (l ∣ r) (Inr x) = Inr (integralTree r x)
  integralTree (l · r) t with matchEpsilon l
  integralTree (l · r) (Inl (fst , snd)) | yes p = integralTree l fst , snd
  integralTree (l · r) (Inr x) | yes (y , m) = y , integralTree r x
  integralTree (l · r) (fst , snd) | no ¬p = integralTree l fst , snd
  integralTree (r *) (fst , snd) = integralTree r fst :: snd
\end{code}
%endif

The description of a derivative-based matcher is stateful:
we perform a step by \emph{removing} a character from the input string.
To match the description, we introduce new effect |Parser| which provides a parser-specific interface to this state.
The |Parser| effect has one command |Symbol| that returns a |Maybe Char|.
Calling |Symbol| will return |just| the head of the unparsed remainder (advancing the string by one character) or |nothing| if the string has been totally consumed.
\begin{code}
  data CParser : Set where
    Symbol : CParser
  RParser : CParser -> Set
  RParser Symbol = Maybe Char
  Parser = mkSig CParser RParser

  symbol : (Forall(es)) ⦃ iP : Parser ∈ es ⦄ -> Free es (Maybe Char)
  symbol ⦃ iP ⦄ = Op iP Symbol Pure
\end{code}

The code for the new parser, |dmatch|, is now only a few lines long.  When the
input contains at least one character, we use the derivative to match the first
character and recurse; when the input string is empty, we check that the
expression matches the empty string.
%if style == newcode
\begin{code}
-- Dependent If-Then-Else syntax inspired by Lean
  dite : ∀ {l k} {P : Set l} {a : Set k} → Dec P → (P → a) → (¬ P → a) → a
  dite P t f = if' P then t else f
  syntax dite P (λ p → t) f = if p <- P then t else f
\end{code}
%endif
\begin{code}
  dmatch : (Forall(es)) ⦃ iP : Parser ∈ es ⦄ ⦃ iND : Nondet ∈ es ⦄  -> (RecArr Regex es tree)
  dmatch r = symbol >>= maybe
    (λ x -> integralTree r <$> call (hiddenInstance(∈Head)) (d r /d x))
    (if p <- matchEpsilon r then Pure (Sigma.fst p) else (hiddenConst(fail)))
\end{code}
Here, |maybe f y| takes a |Maybe| value and applies |f| to the value in |just|, or returns |y| if it is |nothing|.
Although the parser is easily seen to terminate in the intended semantics
(since a character is removed from the input string between each recursive
call), a semantics where the call to |symbol| always returns |just| a character
causes |dmatch| to diverge. The termination of |dmatch| is not a syntactical
property, as reflected by the use of the recursive |call| in its definition,
and the custom arrow used in the type of functions defined using general recursion.

Adding the new effect |Parser| to our repertoire thus requires specifying its semantics.
We gave the effects |Nondet| and |Rec| predicate transformer semantics in the form of a |PT| record.
After introducing the |Parser| effect, the pre- and postcondition become more complicated:
not only do they reference the `pure' arguments and return values (here of type |r : Regex| and |Tree r| respectively),
there is also the current state, containing a |String|, to keep track of.
With these augmented predicates, the predicate transformer semantics for the |Parser| effect can be given as:
\begin{code}
  ptParser : (c : CParser) -> (RParser c -> String -> Set) -> String -> Set
  ptParser Symbol P Nil        = P nothing   Nil
  ptParser Symbol P (x :: xs)  = P (just x)  xs
\end{code}

In this article, we want to demonstrate the modularity of predicate transformer semantics,
allowing us to introduce new notions without having to rework existing constructions.
To illustrate how the semantics mesh well with other forms of semantics,
we do \emph{not} use |ptParser| as semantics for |Parser| in the remainder.
We give denotational semantics, in the form of an \emph{effect handler} for |Parser|~\cite{algebraic-effect-handlers,effect-handlers-in-scope}:
\begin{code}
  hParser : (Forall(es)) ⦃ iND : Nondet ∈ es ⦄ (c : CParser) -> String -> Free es (RParser c × String)
  hParser Symbol Nil        = Pure (nothing  , Nil)
  hParser Symbol (x :: xs)  = Pure (just x   , xs)
\end{code}
The function |handleRec| folds a given handler over a recursive definition,
allowing us to handle the |Parser| effect in |dmatch|.
\begin{code}
  handleRec : (Forall(C R es s)) ((c : C) -> s -> Free es (R c × s)) ->
    (Forall(a b)) (RecArr a (mkSig C R :: es) b) -> (RecArrBinding (x) (a × s) es (b (Pair.fst x)))
  dmatch' : (Forall(es)) ⦃ iND : Nondet ∈ es ⦄ → (RecArrBinding (x) (Regex × String) es (tree (Pair.fst x)))
  dmatch' = handleRec hParser (dmatch (hiddenInstance(∈Head)))
\end{code}
%if style == newcode
\begin{code}
  handleRec h f (x , s) = Pair.fst <$> handleRec' h (f x) s
    where
    liftE : ∀ {e es a} -> Free es a -> Free (e :: es) a
    liftE (Pure x) = Pure x
    liftE (Op i c k) = Op (∈Tail i) c (λ x -> liftE (k x))

    handleRec' : ∀ {C R es s} -> ((c : C) -> s -> Free es (R c × s)) -> forall { I O a } -> (Free (Rec I O :: mkSig C R :: es) a) -> s -> (Free (Rec (I × s) (O ∘ Pair.fst) :: es) (a × s))
    handleRec' h (Pure x) t = Pure (x , t)
    handleRec' h (Op ∈Head i k) t = Op ∈Head (i , t) (λ x -> handleRec' h (k x) t)
    handleRec' h (Op (∈Tail ∈Head) c k) t = liftE (h c t) >>= (λ xt -> handleRec' h (k (Pair.fst xt)) (Pair.snd xt))
    handleRec' h (Op (∈Tail (∈Tail i)) c k) t = Op (∈Tail i) c (λ x -> handleRec' h (k x) t)
\end{code}
%endif
Note that |dmatch'| has exactly the type of the previously defined |match|,
conveniently allowing us to re-use the |wpMatch'| semantics.
In this way, the handler |hParser| ``hides'' the implementation detail that the
|Parser| effect was used.

\section{Proving total correctness} \label{sec:dmatch-correct}
We finish the development process by proving that |dmatch| is correct.
The first step in this proof is that |dmatch| always terminates.
%Since |dmatch| always consumes a character before recursing, the
%number of recursive calls is bounded by the length of the input string.
%As a result, we can handle the recursive effect by unfolding the
%definition a bounded number of times. In the remainder of this
%section, we will make this argument precise and relate the |dmatch|
%function above to the |match| function defined previously.
% Intuitively, this means that |dmatch| terminates on all input.  If we
% are going to give a formal proof of termination, we should first
% determine the correct formalization of this notion.  For that, we need
% to consider what it means to have no recursion in the unfolded
% computation.  A definition for the |while| loop using general
% recursion looks as follows:
% \begin{code}
%   while : (Forall(es a)) ⦃ iRec : Rec a (K a) ∈ es ⦄ ->
%     (a -> Bool) -> (a -> a) -> (a -> Free es a)
%   while cond body i = if cond i then Pure i else (call (body i))
% \end{code}
% We would like to say that some |while| loops terminate, yet the definition of |while| always contains a |call| in it.
% Thus, the requirement should not be that there are no more calls left,
% but that these calls are irrelevant.
%
% Wouter: ik vond de discussie hierboven wat verwarrend. Ik heb
% geprobeerd om het te integreren met de uitleg hieronder.
% Intuitively, we could say that a definition |S| calling |f| terminates
% if we make the unfolded definition into a |Partial| computation by replacing |call| with |fail|,
% the definition terminates if the |Partial| computation still works the same, i.e. it refines |S|.
% However, this mixes the concepts of correctness and termination.
% We want to see that the |Partial| computation gives some output,
% without caring about which output this is.
To express the termination of a recursive computation, we define the following
predicate, |terminates-in|: 
\begin{code}
  terminates-in : (Forall(I O es a)) (pts : PTs es) (f : (RecArr I es O)) (S : Free (Rec I O :: es) a) → Nat → Set
  terminates-in pts f (Pure x)            n         = ⊤
  terminates-in pts f (Op ∈Head c k)      Zero      = ⊥
  terminates-in pts f (Op ∈Head c k)      (Succ n)  = terminates-in pts f (f c >>= k) n
  terminates-in pts f (Op (∈Tail i) c k)   n        =
    lookupPT pts i c (λ x → terminates-in pts f (k x) n)
\end{code}
Given a program |S| that calls the recursive
function |f : (RecArr I es O)|, we check whether the computation requires no
more than a fixed number of steps to terminate.

Since |dmatch| always consumes a character before recurring,
we can bound the number of recursive calls with the length of the input string.
We formalize this argument in the lemma |dmatchTerminates|.
Note that |dmatch'| is defined using the |hParser| handler,
showing that we can mix denotational and predicate transformer semantics.
The proof goes by induction on this string.
Unfolding the recursive |call| gives |integralTree r <$> dmatch' (d r /d x , xs)|,
which we rewrite using the associativity monad law in a lemma called |terminates-fmap|.
\begin{code}
  dmatchTerminates : (r : Regex) (xs : String) →
    terminates-in (ptAll :: Nil) (dmatch' (hiddenInstance(∈Head)) ) (dmatch' (hiddenInstance(∈Head)) (r , xs)) (length xs)
  dmatchTerminates r Nil with matchEpsilon r
  dmatchTerminates r Nil | yes p  = tt
  dmatchTerminates r Nil | no ¬p  = tt
  dmatchTerminates r (x :: xs) = terminates-fmap (length xs) (dmatch' (hiddenInstance(∈Head)) ((d r /d x) , xs))
    (dmatchTerminates (d r /d x) xs)
    where
    terminates-fmap : (Forall(I O es a b pts)) {f : (RecArr I es O)} {g : a → b} (n : Nat) (S : Free (Rec I O :: es) a) →
      terminates-in pts f S n → terminates-in pts f (g <$> S) n
\end{code}
%if style == newcode
\begin{code}
    assoc : ∀ {es a b c} (S : Free es a) (f : a → Free es b) (g : b → Free es c) → (S >>= f) >>= g == S >>= (λ x → f x >>= g)
    assoc (Pure x) f g = refl
    assoc (Op i c k) f g = cong (Op i c) (extensionality λ x → assoc (k x) f g)
    terminates-fmap n (Pure x) H = H
    terminates-fmap {pts = pts} {f} {g} (Succ n) (Op ∈Head c k) H = subst (λ S → terminates-in pts f S n) (assoc (f c) k (Pure ∘ g)) (terminates-fmap n (f c >>= k) H)
    terminates-fmap {pts = pts} n (Op (∈Tail i) c k) H = lookupMono pts i c _ _ (λ x → terminates-fmap n (k x)) H
\end{code}
%endif

Apart from termination, correctness consists of soundness and completeness: the
parse trees returned by |dmatch| should satisfy the specification given by
the original |Match| relation, and for any string that matches the regular
expression, |dmatch| should return a parse tree.  In the |ptAll| semantics, a
non-deterministic program |S| is refined by |T| if and only if the output values
of |T| are a subset of the output values of |S|; conversely |S| is refined by
|T| in the |ptAny| semantics if and only if the output values of |S| are a
subset of the output values of |T|. These properties allow us to express
program correctness in terms of refinement.

We can show soundness of |dmatch| by proving it refines |match|.  Transitivity
of the refinement relation then allows us to conclude that it also satisfies
the specification given by our original |Match| relation. The first step is to
show that the derivative operator is correct, i.e. |d r /d x| matches those
strings |xs| such that |r| matches |x :: xs|.
\begin{code}
  derivativeCorrect : (Forall(x xs)) ∀ r -> (Forall(y)) Match (d r /d x) xs y -> Match r (x :: xs) (integralTree r y)
\end{code}
The proof is straightforward by induction on the derivation of type |Match (d r /d x) xs y|.
%if style == newcode
\begin{code}
  derivativeCorrect Empty ()
  derivativeCorrect Epsilon ()
  derivativeCorrect {x} (Singleton c) m with x ≟ c
  derivativeCorrect (Singleton c) Epsilon | yes refl = Singleton
  derivativeCorrect (Singleton c) () | no ¬p
  derivativeCorrect (l · r) m with matchEpsilon l
  derivativeCorrect (l · r) (OrLeft (Concat ml mr)) | yes (mlr , plr) = Concat (derivativeCorrect _ ml) mr
  derivativeCorrect (l · r) (OrRight m) | yes (mlr , plr) = Concat plr (derivativeCorrect _ m)
  derivativeCorrect (l · r) (Concat ml mr) | no ¬p = Concat (derivativeCorrect _ ml) mr
  derivativeCorrect (l ∣ r) (OrLeft m) = OrLeft (derivativeCorrect _ m)
  derivativeCorrect (l ∣ r) (OrRight m) = OrRight (derivativeCorrect _ m)
  derivativeCorrect (r *)   (Concat ml mr) = StarConcat (Concat (derivativeCorrect _ ml) mr)
\end{code}
%endif

% Before we can prove the correctness of |dmatch| in terms of |match|, it turns
% out that we also need to describe |match| itself better. The meaning of our
% goal, to show that |match| is refined by |dmatch|, is to prove that the output
% of |dmatch| is a subset of that of |match|. Since |match| makes use of
% |allSplits|, we first prove that all splittings of a string |xs| are in the
% output of |allSplits xs|. This following lemma and |allSplitsSound| together
% show that calling |allSplits xs| is equivalent, under the semantics |wpMatch|, to its
% specification |[[ ⊤ , allSplitsPost xs ]]|.
%if style == newcode
%Wouter: weer een detail dat ik even weg zou laten
\begin{code}
  allSplitsComplete : (xs : String) → (wpMatch (allSplits (hiddenInstance(∈Tail ∈Head)) xs)) ⊑ (wpSpec [[ ⊤ , allSplitsPost xs ]])
\end{code}
\begin{code}
  allSplitsComplete Nil P H = tt , λ
    { (Nil , .Nil) refl → H }
  allSplitsComplete (x :: xs) P H = tt , λ
    { (Nil , .(x :: xs)) refl → Pair.fst H
    ; ((.x :: ys) , zs) refl → Pair.snd (allSplitsComplete xs (λ {(ys , zs) → P ((x :: ys) , zs)}) (wpFromBind (allSplits (ys ++ zs)) _ (Pair.snd H))) (ys , zs) refl}
\end{code}
%endif
% The proof mirrors |allSplits|, performing induction on |xs|.
Using the preceding lemmas, we can prove the partial correctness of |dmatch|.
% by showing it refines |match|.
\begin{code}
  dmatchSound : ∀ r xs -> (wpMatch (match (hiddenInstance(∈Head)) (r , xs))) ⊑ (wpMatch (dmatch' (hiddenInstance(∈Head)) (r , xs)))
\end{code}
Since we need to perform the case distinctions of |match| and of |dmatch|,
the proof is longer than that of |matchSound|.
Despite the length, most of it consists of this case distinction,
then giving a simple argument for each case.
%if style == newcode
\begin{code}
  dmatchSound Empty          Nil             P H = tt
  dmatchSound Empty          (x :: xs)       P H = λ o ()
  dmatchSound Epsilon        Nil             P H = H
  dmatchSound Epsilon        (x :: xs)       P H = λ o ()
  dmatchSound (Singleton c)  Nil             P H = H
  dmatchSound (Singleton c)  (x :: xs)       P H with x ≟ c
  dmatchSound (Singleton c)  (.c :: Nil)     P H | yes refl with c ≟ c
  dmatchSound (Singleton c)  (.c :: Nil)     P H | yes refl | yes refl = λ {o Epsilon -> H}
  dmatchSound (Singleton c)  (.c :: Nil)     P H | yes refl | no ¬p = magic (¬p refl)
  dmatchSound (Singleton c)  (.c :: _ :: _)  P H | yes refl = λ o ()
  dmatchSound (Singleton c)  (_ :: _)        P H | no ¬p = λ o ()
  dmatchSound (l · r)        Nil             P H with matchEpsilon l | matchEpsilon r
  dmatchSound (l · r)        Nil             P H | yes (ml , pl) | yes (mr , pr) = H _ pl _ pr
  dmatchSound (l · r)        Nil             P H | yes (ml , pl) | no ¬pr = tt
  dmatchSound (l · r)        Nil             P H | no ¬pl | yes (mr , pr) = tt
  dmatchSound (l · r)        Nil             P H | no ¬pl | no ¬pr = tt
  dmatchSound (l · r)        (x :: xs)       P (fst , snd) with matchEpsilon l
  ... | yes (ml , pl) = λ
    { (Inl (tl , tr)) (OrLeft (Concat {ys = ys} {zs = zs} lH rH)) →
      Pair.snd (allSplitsComplete (x :: xs)
        (λ { (ys , zs) → wpMatch (call ⦃ ∈Head ⦄ (l , ys) >>= λ y → call ⦃ ∈Head ⦄ (r , zs) >>= λ z → Pure (y , z)) P})
        (wpFromBind {pts = ptRec matchSpec :: ptAll :: Nil} (allSplits ⦃ ∈Tail ∈Head ⦄ (x :: ys ++ zs)) _ (fst , snd))
      ) ((x :: ys) , zs) refl _ (derivativeCorrect l lH) _ rH
    ; (Inr t) (OrRight h) →
      fst _ pl _ (derivativeCorrect r h) }
  ... | no ¬p = λ {
    (y , z) (Concat {ys = ys} {zs = zs} lH rH) →
      Pair.snd (allSplitsComplete (x :: xs)
        (λ { (ys , zs) → wpMatch (call ⦃ ∈Head ⦄ (l , ys) >>= λ y → call ⦃ ∈Head ⦄ (r , zs) >>= λ z → Pure (y , z)) P})
        (wpFromBind {pts = ptRec matchSpec :: ptAll :: Nil} (allSplits ⦃ ∈Tail ∈Head ⦄ (x :: ys ++ zs)) _ (fst , snd))
      ) ((x :: ys) , zs) refl _ (derivativeCorrect l lH) _ rH}
  dmatchSound (l ∣ r)        Nil             P (fst , snd) with matchEpsilon l | matchEpsilon r
  dmatchSound (l ∣ r)        Nil             P (fst , snd) | yes (ml , pl) | yes (mr , pr) = fst ml pl
  dmatchSound (l ∣ r)        Nil             P (fst , snd) | yes (ml , pl) | no ¬pr = fst ml pl
  dmatchSound (l ∣ r)        Nil             P (fst , snd) | no ¬pl | yes (mr , pr) = snd mr pr
  dmatchSound (l ∣ r)        Nil             P (fst , snd) | no ¬pl | no ¬pr = tt
  dmatchSound (l ∣ r) (x :: xs) P (fst , snd) .(Inl _) (OrLeft H) = fst _ (derivativeCorrect l H)
  dmatchSound (l ∣ r) (x :: xs) P (fst , snd) .(Inr _) (OrRight H) = snd _ (derivativeCorrect r H)
  dmatchSound (r *)          Nil             P H = H
  dmatchSound (r *)          (x :: xs)       P H ms (Concat ml mr)
    = H _ (Concat (derivativeCorrect _ ml) mr)
\end{code}
%endif

%With the proof of |dmatchSound| finished, we can conclude that
%|dmatch| always returns a correct parse tree, i.e. that |dmatch| is
%sound.
Although we successfully proved |dmatch| is sound with respect to the |Match|
relation, it is not \emph{complete}: the function |dmatch| never makes a
non-deterministic choice. It will not return all possible parse trees that
satisfy the |Match| relation, only the first tree that it encounters.  We can,
however, prove that |dmatch| will find a parse tree if it exists.  To express
that |dmatch| returns any result at all, we use a trivially true postcondition;
by furthermore replacing the demonic choice of the |ptAll| semantics with the
angelic choice of |ptAny|, we require that |dmatch| \emph{must} return a
result:
\begin{code}
  dmatchComplete : ∀ r xs y → Match r xs y →
    (wp (ptRec matchSpec :: ptAny :: Nil) (dmatch' (hiddenInstance(∈Head)) (r , xs))) (λ _ → ⊤)
\end{code}
The proof is short, since |dmatch| can only |fail| when it encounters
an empty string and a regular expression that does not match the empty
string, which contradicts the assumption |Match r xs y|:
\begin{code}
  dmatchComplete r Nil y H with matchEpsilon r
  ... | yes p = tt
  ... | no ¬p = ¬p (_ , H)
  dmatchComplete r (x :: xs) y H y' H' = tt
\end{code}

% Note that |dmatchComplete| does not guarantee that |dmatch|
% terminates: the semantics for the recursive case assume that |dmatch|
%  some value |y'|.

In the proofs of |dmatchSound| and |dmatchComplete|, we demonstrate
the power of predicate transformer semantics for effects: by
separating syntax and semantics, we can easily describe different
aspects (soundness and completeness) of the one definition of
|dmatch|.  Since the soundness and completeness result we have proved
imply partial correctness, and partial correctness and termination
imply total correctness, we can conclude that |dmatch| is a totally
correct parser for regular languages.

% TODO Wouter: misschien goed om expliciet te benadrukken hoe
% refinement van de all/any predicate transformers
% completeness/soundness garanderen?

\section{Discussion}

\subsection*{Related work}
The refinement calculus has traditionally been used to verify imperative programs~\cite{prog-from-spec}.
In this paper, however, we show how many of the ideas from the refinement calculus can also be used in the verification of functional programs~\cite{pt-semantics-for-effects}.
The \emph{Dijkstra monad}, introduced in the language F$\star$, also uses a predicate transformer semantics for verifying effectful programs
by collecting the proof obligations for verification~\cite{dijkstra-monad, dijkstra-monads-for-free, dijkstra-monads-for-all}.
This paper demonstrates how similar verification efforts can be undertaken directly in an interactive theorem prover such as Agda.
The separation of syntax and semantics in our approach allows for verification to be performed in several steps,
such as we did for |dmatchTerminates|, |dmatchSound| and |dmatchComplete|, adding new effects as we need them.

Our running example of the regular expression parser is inspired by the development of a regular expression parser by \citet{harper-regex}.
More recently, \citet{intrinsic-verification-regex} adapted the Functional Pearl to Agda.
A direct translation of \citeauthor{harper-regex}'s definitions is not possible:
they are rejected by Agda's termination checker because they are not structurally recursive.
\citeauthor{intrinsic-verification-regex} show how the defunctionalization of Harper's matcher, written in
continuation-passing style, is 
accepted by Agda's termination checker.

Formally verified parsers for a more general class of languages have been developed before:
\citet{total-parser-combinators, firsov-certification-context-free-grammars, simple-functional-cfg-parsing}, among others, have
previously shown how to verify parsers developed in a functional language.
In these developments, semantics are defined specialized to the domain of parsing,
while our semantics arise from combining a generic set of effect semantics.
Furthermore, we allow our parsers to be written using general recursion directly, whereas most existing approaches
deal with termination syntactically, either by incorporating delay and force operators in the grammar,
or explicitly passing around a proof of termination in the definition of the parser.
The modularity of our setup allows us to separate partial and total correctness cleanly.

There are various ways to represent a combination of effects such as used in parsers.
A traditional approach is to use \emph{monad transformers} to add each effect in turn, producing a complicated monad that incorporates all required operations~\cite{monad-transformers}.
More recently, \emph{graded monads} were introduced as a way to indicate more precisely the effects used in a specific computation~\cite{embedding-effect-systems,effects-and-monads}.
With some slight changes to the types of |Pure| and |_>>=_|, the |Free| monad can be viewed as graded over the free monoid |List Sig| generated by the type of effect signatures.
As this monad containing the computation is freely generated, it does not require us to assign any semantics to the effects ahead of time.

% The partial correctness proof of |match| uses a specification expressed as a postcondition,
% based on the inductive relation representing the language of a given regular expression.
% Where we use non-determinism to handle the concatenation operator,
% \citeauthor{harper-regex} uses a continuation-passing parser for control flow.
% Since the continuations take the unparsed remainder of the string,
% they correspond almost directly to the |Parser| effect we introduce later.
% Another main difference between our implementation and \citeauthor{harper-regex}'s
% is in the way the non-termination of |match| is resolved.
% \citeauthor{harper-regex} uses the derivative operator to rewrite the expression in a standard form
% which ensures that the |match| function terminates.
% We use the derivative operator to implement a different matcher |dmatch| which is easily proved to be terminating,
% then show that |match| is refined by |dmatch|, showing that |dmatch| is also sound with respect to the specification of |match|.
% The final major difference is that \citeauthor{harper-regex} uses manual verification of the program and our work is formally computer-verified.
% % Although our development takes more work, the correctness proofs give more certainty than the informal arguments made by \citeauthor{harper-regex}.
% % In general, choosing between informal reasoning and formal verification will always be a trade-off between speed and accuracy.

%Our development of |dmatch| uses a combination of |Parser| and |Rec| effects to handle recursion in regular expressions.
%Alternate solutions include representing the language in a coinductive type.
%Coinductive types were applied to the domain of parsing in the form of a \emph{coinductive trie}~\cite{coinductive-trie}.
%Similarly, \citet{ooagda} use a coinductive type to represent effectful programs with arbitrarily large input.
%These two coinductive constructions carry proofs of productivity, in the form of sized types, in their definitions,
%again mixing syntax and semantics.

\subsection*{Open issues}
This paper builds upon our previous results \cite{pt-semantics-for-effects} by
demonstrating their use in non-trivial development. In the process, we show how to
\emph{combine} predicate transformer semantics and reason about
programs using a combination of effects.

Our approach relies on using coproducts to combine effect syntax. The
interaction between different effects means applying handlers in a different
order can result in different semantics.  We assign predicate transformer
semantics to a combination of effects all at once, specifying their interaction
explicitly---but we would still like to explore how to handle effects
one-by-one, allowing for greater flexibility when assigning semantics to
effectful programs~\cite{modular-algebraic-effects, effect-handlers-in-scope}.

% Can we assign semantics to effects one by one, such that they interact in a similar way as handlers do? 
% Still, the choice to verify
% parsers was made expecting that predicate transformer semantics should apply
% easily to them.  Whether we can do the same verification for practical programs
% is not yet answerable with an unanimous ``yes''.
% Perhaps a translation of ``er valt iets af te dingen aan het idee dat we een praktisch programma verifiëren'' is more apt.

\subsection*{Conclusions}
In conclusion, we have illustrated the approach to developing verified software
in a proof assistant using a predicate transformer semantics for effects for a
non-trivial example.  We believe this approach enables us to add new effects in
a modular fashion, while still being able to re-use any existing proofs.  Along
the way, we demonstrated how to combine different effects and define different
semantics for these effects, without impacting existing definitions.  As a
result, the verification effort---while conceptually more challenging at
times---remains fairly modular.

% We note the absence of any large engineering effort needed for our development,
% as we expected before writing this paper~\cite{pt-semantics-for-effects}.
% The optimist can conclude that the elegance of our framework caused it to prevent the feared level of complication;
% the pessimist can conclude that the real hard work will be required as soon as we encounter a real-world application.

\paragraph{Acknowledgements}
T. Baanen has received funding from the NWO under the Vidi program (project No. 016.Vidi.189.037, Lean Forward).

\printbibliography

\appendix

\ifdefined\includeCFGs

\section{Parsing as effect} \label{sec:parser}
%if style == newcode
\begin{code}
module Parser where
  open Combinations
  open Sig
\end{code}
%endif
In the previous sections, we wrote parsers as nondeterministic functions.
For more complicated classes of languages than regular expressions, explicitly passing around the string to be parsed becomes cumbersome quickly.
The traditional solution is to switch from nondeterminism to stateful nondeterminism, where the state contains the unparsed portion of the string~\cite{hutton}.
The combination of nondeterminism and state can be represented by the |ListOfSuccesses| monad:
\begin{code}
  ListOfSuccesses : Set → Set
  ListOfSuccesses a = String → List (a × String)
\end{code}

Since our development makes use of algebraic effects,
we can introduce the effect of mutable state without having to change existing definitions.
We introduce this using the |Parser| effect, which has one command |Symbol|.
Calling |Symbol| will return the current symbol in the state (advancing the state by one) or fail if all symbols have been consumed.
\begin{code}
  data CParser : Set where
    Symbol : CParser
  RParser : CParser -> Set
  RParser Symbol = Char
  Parser = mkSig CParser RParser

  symbol : (Forall(es)) ⦃ iP : Parser ∈ es ⦄ -> Free es Char
  symbol ⦃ iP ⦄ = Op iP Symbol Pure
\end{code}
We could add more commands such as |EOF| for detecting the end of the input, but we do not need them in the current development.
In the semantics we will define that parsing was successful if the input string has been completely consumed.

Note that |Parser| is not sufficient by itself to implement even simple parsers such as |dmatch|:
we need to be able to choose between parsing the next character or returning a value for the empty string.
This is why we usually combine |Parser| with nondeterminism and general recursion.

The denotational semantics of a parser in the |Free| monad take the form of a fold,
handling each command in the |Parser| monad.
\begin{code}
  runParser : (Forall(a)) Free (Nondet :: Parser :: Nil) a -> ListOfSuccesses a
  runParser (Pure x) Nil = (x , Nil) :: Nil
  runParser (Pure x) (_ :: _) = Nil
  runParser (Op ∈Head Fail k) xs = Nil
  runParser (Op ∈Head Choice k) xs =
    runParser (k True) xs ++ runParser (k False) xs
  runParser (Op (∈Tail ∈Head) Symbol k) Nil = Nil
  runParser (Op (∈Tail ∈Head) Symbol k) (x :: xs) = runParser (k x) xs
\end{code}

In this article, we are more interested in the predicate transformer semantics of |Parser|.
Since the semantics of |Parser| refer to a state, the predicates depend on this state.
We can incorporate a mutable state of type |s| in predicate transformer semantics
by replacing the propositions in |Set| with predicates over the state in |s → Set|.
We define the resulting type of stateful predicate transformers for an effect with signature |e| to be |PTS s e|, as follows:
\begin{code}
  record PTS (s : Set) (e : Sig) : Set₁ where
    constructor mkPTS
    field
      pt : (c : C e) → (R e c → s → Set) → s → Set
      mono : ∀ c P P' → (∀ x t → P x t → P' x t) → pt c P ⊆ pt c P'
\end{code}
%if style == newcode
\begin{code}
  data PTSs (s : Set) : List Sig -> Set₁ where
    Nil : PTSs s Nil
    _::_ : ∀ {e es} -> PTS s e -> PTSs s es -> PTSs s (e :: es)

  lookupPTS : ∀ {s C R es} (pts : PTSs s es) (i : mkSig C R ∈ es) -> (c : C) -> (R c -> s -> Set) -> s -> Set
  lookupPTS (pt :: pts) ∈Head c P t = PTS.pt pt c P t
  lookupPTS (pt :: pts) (∈Tail i) c P t = lookupPTS pts i c P t
  lookupMono : ∀ {s C R es} (pts : PTSs s es) (i : mkSig C R ∈ es) -> ∀ c P P' → (∀ x t → P x t → P' x t) → ∀ t → lookupPTS pts i c P t → lookupPTS pts i c P' t
  lookupMono (pt :: pts) ∈Head = PTS.mono pt
  lookupMono (pt :: pts) (∈Tail i) = lookupMono pts i
\end{code}
%endif
If we define |PTSs| and |lookupPTS| analogously to |PTs| and |lookupPT|, 
we have found a predicate transformer semantics that incorporates the current state:
\begin{code}
  wpS' : (Forall(s es a)) (pts : PTSs s es) -> Free es a -> (a -> s -> Set) -> s -> Set
  (wpS pts (Pure x)) P = P x
  (wpS pts (Op i c k)) P = lookupPTS pts i c (λ x -> (wpS pts (k x)) P)
\end{code}

In this definition for |wpS'|, we assume that all effects share access to one mutable variable of type |s|.
We can allow for more variables by setting |s| to be a product type over the effects.
With a suitable modification of the predicate transformers,
we could set it up so that each effect can only modify its own associated variable.
Thus, the previous definition is not limited in generality by writing it only for one variable.

To give the predicate transformer semantics of the |Parser| effect,
we need to choose the meaning of failure, for the case where the next character is needed
and all characters have already been consumed.
Since we want all results returned by the parser to be correct,
we use demonic choice and the |ptAll| predicate transformer
as the semantics for |Nondet|.
Using |ptAll|'s semantics for the |Fail| command gives the following semantics for the |Parser| effect.
\begin{code}
  ptParse : PTS String Parser
  PTS.pt ptParse Symbol P Nil = ⊤
  PTS.pt ptParse Symbol P (x :: xs) = P x xs
\end{code}
%if style == newcode
\begin{code}
  PTS.mono ptParse Symbol P Q imp Nil asm = tt
  PTS.mono ptParse Symbol P Q imp (x :: xs) asm = imp x xs asm
  ptAll : ∀ {s} -> PTS s Nondet
  PTS.pt ptAll Fail P _ = ⊤
  PTS.pt ptAll Choice P s = P True s ∧ P False s
  PTS.mono ptAll Fail P Q imp t tt = tt
  PTS.mono ptAll Choice P Q imp t (fst , snd) = imp _ _ fst , imp _ _ snd
\end{code}
%endif

With the predicate transformer semantics of |Parser|,
we can define the language accepted by a parser in the |Free| monad as a predicate over strings:
a string |xs| is in the language of a parser |S| if the postcondition ``all characters have been consumed'' is satisfied.
\begin{code}
  empty? : (Forall(l)) (implicit(a : Set l)) List a -> Set
  empty? Nil = ⊤
  empty? (_ :: _) = ⊥

  _∈[_] : (Forall(a)) String -> Free (Nondet :: Parser :: Nil) a -> Set
  xs ∈[ S ] = (wpS (ptAll :: ptParse :: Nil) S) (λ _ -> empty?) xs
\end{code}

\section{Parsing context-free languages} \label{sec:fromProductions}
In Section \ref{sec:dmatch}, we developed and formally verified a parser for regular languages.
The class of regular languages is small, and does not include most programming languages.
A class of languages that is more expressive than the regular languages,
while remaining tractable in parsing is that of the \emph{context-free language}.
The expressiveness of context-free languages is enough to cover most programming languages used in practice~\cite{dragon-book}.
We will represent context-free languages in Agda by giving a grammar in the style of \citet{dependent-grammar},
in a similar way as we represent a regular language using an element of the |Regex| type.
Following their development, we parametrize our definitions over a collection of non-terminal symbols.
%if style == newcode
\begin{code}
open import Relation.Binary
\end{code}
%endif
\begin{code}
record GrammarSymbols : Set₁ where
  field
    Nonterm : Set
    ⟦_⟧ : Nonterm -> Set
    _≟n_ : Decidable {A = Nonterm} _==_
\end{code}
The elements of the type |Char| are the \emph{terminal} symbols.
The elements of the type |Nonterm| are the \emph{non-terminal} symbols, representing the language constructs.
As for |Char|, we also need to be able to decide the equality of non-terminals.
The (disjoint) union of |Char| and |Nonterm| gives all the symbols that we can use in defining the grammar.
%if style == newcode
\begin{code}
module Grammar (gs : GrammarSymbols) where
  open Parser hiding (Symbol)
  open GrammarSymbols gs
\end{code}
%endif
\begin{code}
  Symbol = Either Char Nonterm
  Symbols = List Symbol
\end{code}
For each non-terminal |A|, our goal is to parse a string into a value of type |⟦ A ⟧|,
based on a set of production rules.
A production rule $A \to xs$ gives a way to expand the non-terminal |A| into a list of symbols |xs|,
such that successfully matching each symbol of |xs| with parts of a string
gives a match of the string with |A|.
Since matching a non-terminal symbol |B| with a (part of a) string results in a value of type |⟦ B ⟧|,
a production rule for |A| is associated with a \emph{semantic function} that takes all values arising from submatches
and returns a value of type |⟦ A ⟧|,
as expressed by the following type:
\begin{code}
  ⟦_∥_⟧ : Symbols -> Nonterm -> Set
  ⟦ Nil           ∥ A ⟧ = ⟦ A ⟧
  ⟦ Inl x  :: xs  ∥ A ⟧ = ⟦ xs ∥ A ⟧
  ⟦ Inr B  :: xs  ∥ A ⟧ = ⟦ B ⟧ -> ⟦ xs ∥ A ⟧
\end{code}
Now we can define the type of production rules. A rule of the form $A \to B c D$ is represented as |prod A (Inr B :: Inl c :: Inr D :: Nil) f| for some |f|.
\begin{code}
  record Prod : Set where
    constructor prod
    field
      lhs : Nonterm
      rhs : Symbols
      sem : ⟦ rhs ∥ lhs ⟧
\end{code}
%if style == newcode
\begin{code}
  Prods = List Prod
\end{code}
%endif
We use the abbreviation |Prods| to represent a list of productions,
and a grammar will consist of the list of all relevant productions.

We want to show that a generally recursive function making use of the effects |Parser| and |Nondet| can parse any context-free grammar.
To show this claim, we implement a function |fromProds| that constructs a parser for any context-free grammar given as a list of |Prod|s,
then formally verify the correctness of |fromProds|.
Our implementation mirrors the definition of the |generateParser| function by \citeauthor{dependent-grammar},
differing in the naming and in the system that the parser is written in:
our implementation uses the |Free| monad and algebraic effects, while \citeauthor{dependent-grammar} use a monad |Parser| that is based on parser combinators.
%if style == newcode
\begin{code}
module FromProds (gs : GrammarSymbols) (prods : Grammar.Prods gs) where
  open Parser hiding (Symbol)
  open GrammarSymbols gs
  open Grammar gs
  open Combinations
\end{code}
%endif

We start by defining two auxiliary types, used as abbreviations in our code.
\begin{code}
  FreeParser = Free (mkSig Nonterm ⟦_⟧ :: Nondet :: Parser :: Nil)

  record ProdRHS (A : Nonterm) : Set where
    constructor prodrhs
    field
      rhs : Symbols
      sem : ⟦ rhs ∥ A ⟧
\end{code}

The core algorithm for parsing a context-free grammar consists of the following functions,
calling each other in mutual recursion:
\begin{code}
  fromProds    : (A : Nonterm) -> FreeParser ⟦ A ⟧
  filterLHS    : (A : Nonterm) -> Prods -> List (ProdRHS A)
  fromProd     : (Forall(A)) ProdRHS A -> FreeParser ⟦ A ⟧
  buildParser  : (Forall(A)) (xs : Symbols) -> FreeParser (⟦ xs ∥ A ⟧ -> ⟦ A ⟧)
  exact        : (Forall(a)) a -> Char -> FreeParser a
\end{code}
The main function is |fromProds|: given a non-terminal,
it selects the productions with this non-terminal on the left hand side using |filterLHS|,
and makes a nondeterministic choice between them.
\begin{code}
  filterLHS A Nil = Nil
  filterLHS A (prod lhs rhs sem :: ps) with A ≟n lhs
  ... | yes refl  = prodrhs rhs sem :: filterLHS A ps
  ... | no _      = filterLHS A ps

  fromProds A = choices (hiddenInstance(∈Tail ∈Head)) (map fromProd (filterLHS A prods))
\end{code}
The |choices| operator takes a list of computations and nondeterministically chooses one of them to execute.

The function |fromProd| takes a single production and tries to parse the input string using this production.
It then uses the semantic function of the production to give the resulting value.
\begin{code}
  fromProd (prodrhs rhs sem) = buildParser rhs >>= λ f → Pure (f sem)
\end{code}
The function |buildParser| iterates over the |Symbols|, calling |exact| for each literal character symbol,
and making a recursive |call| to |fromProds| for each non-terminal symbol.
\begin{code}
  buildParser Nil = Pure id
  buildParser (Inl x  :: xs) = exact tt x >>= λ _ -> buildParser xs
  buildParser (Inr B  :: xs) = do
    x <- call (hiddenInstance(∈Head)) B
    o <- buildParser xs
    Pure λ f -> o (f x)
\end{code}
Finally, |exact| uses the |symbol| command to check that the next character in the string is as expected,
and |fail|s if this is not the case.
\begin{code}
  exact x t = symbol (hiddenInstance(∈Tail (∈Tail ∈Head))) >>= λ t' → if' t ≟ t' then (hiddenConst(Pure x)) else (hiddenConst(fail (hiddenInstance(∈Tail ∈Head))))
\end{code}

\section{Partial correctness of the parser} \label{sec:partialCorrectness}
Partial correctness of the parser is relatively simple to show,
as soon as we have a specification.
Since we want to prove that |fromProds| correctly parses any given context free grammar given as an element of |Prods|,
the specification consists of a relation between many sets:
the production rules, an input string, a non-terminal, the output of the parser, and the remaining unparsed string.
Due to the many arguments, the notation is unfortunately somewhat unwieldy.
To make it a bit easier to read, we define two relations in mutual recursion,
one for all productions of a non-terminal,
and for matching a string with a single production rule.
%if style == newcode
\begin{code}
module Correctness (gs : GrammarSymbols) where
  open Parser hiding (Symbol)
  open GrammarSymbols gs
  open Grammar gs
  open Combinations
  open FromProds gs using (FreeParser; fromProds)

  data _⊢_∈⟦_⟧=>_,_ (prods : Prods) : String -> (A : Nonterm) -> ⟦ A ⟧ -> String -> Set
  data _⊢_~_=>_,_ (prods : Prods) {A : Nonterm} : String -> (ps : Symbols) -> (⟦ ps ∥ A ⟧ -> ⟦ A ⟧) -> String -> Set
\end{code}
%endif

\begin{code}
  data _⊢_∈⟦_⟧=>_,_ prods where
    Produce :  (Forall(lhs rhs sem xs ys f)) prod lhs rhs sem ∈ prods ->
               prods ⊢ xs ~ rhs => f , ys ->
               prods ⊢ xs ∈⟦ lhs ⟧=> f sem , ys
  data _⊢_~_=>_,_ prods where
    Done :     (Forall(xs)) prods ⊢ xs ~ Nil => id , xs
    Next :     (Forall(x xs ys ps o)) prods ⊢ xs ~ ps => o , ys ->
               prods ⊢ (x :: xs) ~ (Inl x :: ps) => o , ys
    Call :     (Forall(A ps xs ys zs f o)) prods ⊢ xs ∈⟦ A ⟧=> o , ys ->
               prods ⊢ ys ~ ps => f , zs ->
               prods ⊢ xs ~ (Inr A :: ps) => (λ g -> f (g o)) , zs
\end{code}
%if style == newcode
\begin{code}
  ptRec : ∀ {a : Set} {I : Set} {O : I -> Set} -> ((i : I) -> a -> O i -> a -> Set) -> PTS a (Rec I O)
  PTS.pt (ptRec R) i P s = ∀ o s' -> R i s o s' -> P o s'
  PTS.mono (ptRec R) c P Q imp t asm o t' h = imp _ _ (asm _ _ h)

  record StateSpec (s a : Set) : Set₁ where
    constructor [[_,_]]
    field
      pre : s -> Set
      post : s -> a -> s -> Set

  wpSpec : {s a : Set} -> StateSpec s a -> (a -> s -> Set) -> s -> Set
  wpSpec [[ pre , post ]] P t = pre t ∧ (∀ o t' -> post t o t' -> P o t')

  _⊑_ : {s a : Set} (pt1 pt2 : (a -> s -> Set) -> s -> Set) -> Set₁
  pt1 ⊑ pt2 = ∀ P t -> pt1 P t -> pt2 P t
\end{code}
%endif
%if style == newcode
\begin{code}
  parserSpec : (prods : Prods) (A : Nonterm) (xs : String) -> ⟦ A ⟧ -> String -> Set
  parserSpec prods A xs o ys = prods ⊢ xs ∈⟦ A ⟧=> o , ys

  pts : Prods -> PTSs (String) _
  wpFromProd : (Forall(a)) (prods : Prods) -> FreeParser prods a -> (a -> String -> Set) -> String -> Set
\end{code}
%endif
With these relations, we can define the specification |parserSpec| to be equal to |_⊢_∈⟦_⟧=>_,_| (up to reordering some arguments),
and show that |fromProds| refines this specification.
To state that the refinement relation holds, we first need to determine the semantics of the effects.
We choose |ptAll| as the semantics of nondeterminism, since we want to ensure all output of the parser is correct.
\begin{code}
  pts prods = ptRec (parserSpec prods) :: ptAll :: ptParse :: Nil

  wpFromProd prods S = (wpS (pts prods) S)

  partialCorrectness : (prods : Prods) (A : Nonterm) ->
    (wpSpec [[ (hiddenConst(⊤)) , (parserSpec prods A) ]]) ⊑ (wpFromProd prods (fromProds prods A))
\end{code}

%if style == newcode
\begin{code}
  consequence : ∀ {a b s es} (pts : PTSs s es) {P} (mx : Free es a) (f : a -> Free es b) ->
    ∀ t -> wpS pts mx (λ x t -> wpS pts (f x) P t) t == wpS pts (mx >>= f) P t
  consequence pts (Pure x) f t = refl
  consequence pts (Op i c k) f t = cong (λ P -> lookupPTS pts i c P t) (extensionality λ x -> extensionality λ t -> consequence pts (k x) f t)

  wpToBind : ∀ {a b s es} {pts : PTSs s es} {P} (mx : Free es a) (f : a -> Free es b) ->
    ∀ t -> wpS pts mx (λ x t -> wpS pts (f x) P t) t -> wpS pts (mx >>= f) P t
  wpToBind {pts = pts} mx f t H = subst id (consequence pts mx f t) H

  wpFromBind : ∀ {a b s es} {pts : PTSs s es} {P} (mx : Free es a) (f : a -> Free es b) ->
    ∀ t -> wpS pts (mx >>= f) P t -> wpS pts mx (λ x t -> wpS pts (f x) P t) t
  wpFromBind {pts = pts} mx f t H = subst id (sym (consequence pts mx f t)) H
  partialCorrectness prods A P xs H = filterStep prods A id P xs H
    where
    open FromProds gs
\end{code}
%endif
Let us fix the production rules |prods|.
How do we prove the partial correctness of a parser for |prods|?
Since the structure of |fromProds| is of a nondeterministic choice between productions to be parsed,
and we want to show that all alternatives for a choice result in success,
we will first give a lemma expressing the correctness of each alternative.
Correctness in this case is expressed by the semantics of a single production rule,
i.e. the |_⊢_~_=>_,_| relation.
Thus, we want to prove the following lemma:
\begin{code}
    parseStep : ∀ A xs P str ->
      (∀ o str' -> prods ⊢ str ~ xs => o , str' -> P o str') ->
      (wpFromProd prods (buildParser prods xs)) P str
\end{code}
The lemma can be proved by reproducing the case distinctions used to define |buildParser|;
there is no complication apart from having to use the |wpToBind| lemma to deal with the |_>>=_| operator in a few places.
\begin{code}
    parseStep A Nil P t H = H id t Done
    parseStep A (Inl x :: xs) P Nil H = tt
    parseStep A (Inl x :: xs) P (x' :: t) H with x ≟ x'
    ... | yes refl = parseStep A xs P t λ o t' H' -> H o t' (Next H')
    ... | no ¬p = tt
    parseStep A (Inr B :: xs) P t H o t' Ho =
      wpToBind (buildParser prods xs) _ _
        (parseStep A xs _ t' λ o' str' Ho' → H _ _ (Call Ho Ho'))
\end{code}

To combine the |parseStep| for each of the productions that the nondeterministic choice is made between,
it is tempting to define another lemma |filterStep| by induction on the list of productions.
But we must be careful that the productions that are used in the |parseStep| are the full list |prods|,
not the sublist |prods'| used in the induction step.
Additionally, we must also make sure that |prods'| is indeed a sublist,
since using an incorrect production rule in the |parseStep| will result in an invalid result.
Thus, we parametrize |filterStep| by a list |prods'| and a proof that it is a sublist of |prods|.
Again, the proof uses the same distinction as |fromProds| does,
and uses the |wpToBind| lemma to deal with the |_>>=_| operator.
\begin{code}
    filterStep : ∀ prods' A -> ((Forall(p)) p ∈ prods' -> p ∈ prods) ->
      (wpSpec [[ (hiddenConst(⊤)) , (parserSpec prods A) ]]) ⊑ (wpFromProd prods (choices (hiddenInstance(∈Tail ∈Head)) (map (fromProd prods) (filterLHS prods A prods'))))
    filterStep Nil A subset P xs H = tt
    filterStep (prod lhs rhs sem :: prods') A subset P xs H with A ≟n lhs
    filterStep (prod .A rhs sem :: prods') A subset P xs (_ , H) | yes refl
      = wpToBind (buildParser prods rhs) _ _
      (parseStep A rhs _ xs λ o t' H' → H _ _ (Produce (subset ∈Head) H'))
      , filterStep prods' A (subset ∘ ∈Tail) P xs (_ , H)
    ... | no ¬p = filterStep prods' A (subset ∘ ∈Tail) P xs H
\end{code}

With these lemmas, |partialCorrectness| just consists of applying |filterStep| to the subset of |prods| consisting of |prods| itself.

\section{Termination of the parser} \label{sec:fromProds-terminates}
To show termination we need a somewhat more subtle argument:
since we are able to call the same non-terminal repeatedly,
termination cannot be shown simply by inspecting each alternative in the definition.
Consider the grammar given by $E \rightarrow a E; E \rightarrow b$,
where we see that the string that matches $E$ in the recursive case is shorter than the original string,
but the definition itself can be expanded to unbounded length.
By taking into account the current state, i.e. the string to be parsed, in the variant,
we can show that a decreasing string length leads to termination.

But not all grammars feature this decreasing string length in the recursive case,
with the most pathological case being those of the form $E \to E$.
The issues do not only occur in edge cases: the grammar $E \to E + E; E \to 1$ representing very simple expressions
will already result in non-termination for |fromProds|
as it will go in recursion on the first non-terminal without advancing the input string.
Since the position in the string and current non-terminal together fully determine the state of |fromParsers|,
it will not terminate.
We need to ensure that the grammars passed to the parser do not allow for such loops.

Intuitively, the condition on the grammars should be that they are not \emph{left-recursive},
since in that case, the parser should always advance its position in the string before it encounters the same non-terminal.
This means that the number of recursive calls to |fromProds| is bounded
by the length of the string times the number of different non-terminals occurring in the production rules.
The type we will use to describe the predicate ``there is no left recursion'' is constructively somewhat stronger:
we define a left-recursion chain from $A$ to $B$ to be
a sequence of non-terminals $A, \dots, A_i, A_{i+1}, \dots, B$,
such that for each adjacent pair $A_i, A_{i+1}$ in the chain, there is a production of the form $A_{i+1} \to B_1 B_2 \dots B_n A_i \dots$, where $B_1 \dots B_n$ are all non-terminals.
In other words, we can advance the parser to $A$ starting in $B$ without consuming a character.
Disallowing (unbounded) left recursion is not a limitation for our parsers:
\citet{dependent-grammar} have shown that the \emph{left-corner transform}
can transform left-recursive grammars into an equivalent grammar without left recursion.
Moreover, they have implemented this transform, including formal verification, in Agda.
In this work, we assume that the left-corner transform has already been applied if needed,
so that there is an upper bound on the length of left-recursive chains in the grammar.

We formalize one link of this left-recursive chain in the type |LRec|,
while a list of such links forms the |Chain| data type.
% Get rid of the implicit fields.
\begin{spec}
  record LRec (prods : Prods) (A B : Nonterm) : Set where
    field
      rec : prod A (map Inr xs ++ (Inr B :: ys)) sem ∈ prods
\end{spec}
(We leave |xs|, |ys| and |sem| as implicit fields of |LRec|, since they are fixed by the type of |rec|.)
%if style == newcode
\begin{code}
  record LRec (prods : Prods) (A B : Nonterm) : Set where
    field
      {xs} : List Nonterm
      {ys} : List Symbol
      {sem} : _
      rec : prod B (map Inr xs ++ (Inr A :: ys)) sem ∈ prods
\end{code}
%endif
\begin{code}
  data Chain (prods : Prods) : Nonterm -> Nonterm -> Set where
    Nil : (Forall(A)) Chain prods A A
    _::_ : (Forall(A B C)) LRec prods B A -> Chain prods A C -> Chain prods B C
\end{code}
Now we say that a set of productions has no left recursion if all such chains have an upper bound on their length.
%if style == newcode
\begin{code}
  open import Data.Nat using (_<_; _≤_; _*_; _+_; _∸_; z≤n; s≤s)
  open import Data.Nat.Properties hiding (_≟_)
\end{code}
%endif
\begin{code}
  chainLength : (Forall(prods A B)) Chain prods A B -> Nat
  chainLength Nil = 0
  chainLength (c :: cs) = Succ (chainLength cs)

  leftRecBound : Prods -> Nat -> Set
  leftRecBound prods n = (Forall(A B)) (cs : Chain prods A B) -> chainLength cs < n
\end{code}
If we have this bound on left recursion, we are able to prove termination,
since each call to |fromProds| will be made either after we have consumed an extra character,
or it is a left-recursive step, of which there is an upper bound on the sequence.

This informal proof fits better with a different notion of termination than in the petrol-driven semantics.
The petrol-driven semantics are based on a syntactic argument:
we know a computation terminates because expanding the call tree will eventually result in no more |call|s.
Here, we want to capture the notion that a recursive definition terminates
if all recursive calls are made to a smaller argument, according to a well-founded relation.
\begin{Def}[\cite{aczel-acc}]
In intuitionistic type theory, we say that a relation |_≺_| on a type |a| is well-founded if all elements |x : a| are \emph{accessible},
which is defined by (well-founded) recursion to be the case if all elements in the downset of |x| are accessible.
\begin{code}
  data Acc (hidden(a : Set)) (_≺_ : a → a → Set) : a → Set where
    acc : (Forall(x)) (∀ y → y ≺ x → Acc _≺_ y) → Acc _≺_ x
\end{code}
\end{Def}
To see that this is equivalent to the definition of well-foundedness in set theory,
recall that a relation |_≺_| on a set |a| is well-founded if and only if there is a monotone function from |a| to a well-founded order.
Since all inductive data types are well-founded,
and the termination checker ensures that the argument to |acc| is a monotone function,
there is a function from |x : a| to |Acc _≺_ x| if and only if |_≺_| is a well-founded relation in the set-theoretic sense.

The condition that all calls are made to a smaller argument is related to the notion of a loop \emph{variant}
in imperative languages.
While an invariant is a predicate that is true at the start and end of each looping step,
the variant is a relation that holds between successive looping steps.
\begin{Def}
Given a recursive definition |f : (RecArr I es O)|,
a relation |_≺_| on |C| is a recursive \emph{variant} if for each argument |c|,
and each recursive call made to |c'| in the evaluation of |f c|,
we have |c' ≺ c|.
Formally:
\begin{code}
  variant' : (Forall(s es C R a)) (pts : PTSs s (mkSig C R :: es)) (f : (RecArr C es R))
    (_≺_ : (C × s) → (C × s) → Set)
    (c : C) (t : s) (S : Free (mkSig C R :: es) a) → s → Set
  variant' pts f _≺_ c t (Pure x) t' = ⊤
  variant' pts f _≺_ c t (Op ∈Head c' k) t'
    = ((c' , t') ≺ (c , t)) × lookupPTS pts ∈Head c'
      (λ x → variant' pts f _≺_ c t (k x)) t'
  variant' pts f _≺_ c t (Op (∈Tail i) c' k) t'
    = lookupPTS pts (∈Tail i) c' (λ x → variant' pts f _≺_ c t (k x)) t'

  variant : (Forall(s es C R)) (pts : PTSs s (mkSig C R :: es)) (f : (RecArr C es R)) →
    (_≺_ : (C × s) → (C × s) → Set) → Set
  variant (hidden(s)) (hidden(es)) (hidden(C)) (hidden(R)) pts f _≺_ = ∀ c t → variant' pts f _≺_ c t (f c) t
\end{code}
\end{Def}
Note that |variant| depends on the semantics |pts| we give to the recursive function |f|.
We cannot derive the semantics in |variant| from the structure of |f| as we do for the petrol-driven semantics,
since we do not yet know whether |f| terminates.
Using |variant|, we can define another termination condition on |f|:
there is a well-founded variant for |f|.
\begin{code}
  record Termination (hidden(s es C R)) (pts : PTSs s (mkSig C R :: es)) (f : (RecArr C es R)) : Set₁ where
    field
      _≺_ : (C × s) → (C × s) → Set
      w-f : ∀ c t → Acc _≺_ (c , t)
      var : variant pts f _≺_
\end{code}
A generally recursive function that terminates in the petrol-driven semantics also has a well-founded variant,
given by the well-order |_<_| on the amount of fuel consumed by each call.
The converse also holds: if we have a descending chain of calls |cs| after calling |f| with argument |c|,
we can use induction on the type |Acc _≺_ c| to bound the length of |cs|.
This bound gives the amount of fuel consumed by evaluating a call to |f| on |c|.

In our case, the relation |RecOrder| will work as a recursive variant for |fromProds|:
\begin{code}
  data RecOrder (prods : Prods) : (x y : Nonterm × String) -> Set where
    Left : (Forall(str str' A B)) length str < length str' →
      RecOrder prods (A , str) (B , str')
    Right : (Forall(str str' A B)) length str ≤ length str' →
      LRec prods A B → RecOrder prods (A , str) (B , str')
\end{code}
With the definition of |RecOrder|, we can complete the correctness proof of |fromProds|,
by giving an element of the corresponding |Termination| type.
We assume that the length of recursion is bounded by |bound : Nat|.
\begin{code}
  fromProdsTerminates : ∀ prods bound → leftRecBound prods bound ->
    Termination (pts prods) (fromProds prods)
  Termination._≺_ (fromProdsTerminates prods bound H) = RecOrder prods
\end{code}
To show that the relation |RecOrder| is well-founded,
we need to show that there is no infinite descending chain starting from some non-terminal |A| and string |str|.
The proof is based on iteration on two natural numbers |n| and |k|,
which form an upper bound on the number of allowed left-recursive calls in sequence and unconsumed characters in the string respectively.
Note that the number |bound| is an upper bound for |n| and the length of the input string is an upper bound for |k|.
Since each non-terminal in the production will decrease |n| and each terminal will decrease |k|,
we eventually reach the base case |0| for either.
If |n| is zero, we have made more than |bound| left-recursive calls, contradicting the assumption that we have bounded left recursion.
If |k| is zero, we have consumed more than |length str| characters of |str|, also a contradiction.
\begin{code}
  Termination.w-f (fromProdsTerminates prods bound H) A str
    = acc (go A str (length str) ≤-refl bound Nil ≤-refl)
    where
    go : (Forall(B)) ∀ A str →
      (k : Nat) → length str ≤ k →
      (n : Nat) (cs : Chain prods A B) → bound ≤ chainLength cs + n →
      ∀ y → RecOrder prods y (A , str) → Acc (RecOrder prods) y
\end{code}

%if style == newcode
\begin{code}
    go A Nil Zero ltK n cs H' (A' , str') (Left ())
    go A (_ :: _) Zero () n cs H' (A' , str') (Left lt)

    go A (_ :: _) (Succ k) (s≤s ltK) n cs H' (A' , str') (Left (s≤s lt))
      = acc (go A' str' k (≤-trans lt ltK) bound Nil ≤-refl)
    go A str k ltK Zero cs H' (A' , str') (Right lt cs')
      = magic (<⇒≱ (H cs) (≤-trans H' (≤-reflexive (+-identityʳ _))))
    go A str k ltK (Succ n) cs H' (A' , str') (Right lt c)
      = acc (go A' str' k (≤-trans lt ltK) n (c :: cs) (≤-trans H' (≤-reflexive (+-suc _ _))))

  Termination.var (fromProdsTerminates prods bound H) A str = filterStep prods id A str str ≤-refl
    where
    open FromProds gs prods hiding (FreeParser; fromProds)

    variant-fmap : ∀ {a b C R s es _≺_ c t t'} (pts : PTSs s (mkSig C R :: es)) f S {k : a → b} → variant' pts f _≺_ c t S t' → variant' pts f _≺_ c t (S >>= λ x → Pure (k x)) t'
    variant-fmap pts f (Pure x) H = tt
    variant-fmap pts f (Op ∈Head c k) (fst , snd) = fst , lookupMono pts ∈Head c _ _ (λ x t' H' → variant-fmap pts f (k x) H') _ snd
    variant-fmap pts f (Op (∈Tail i) c k) H = lookupMono pts (∈Tail i) c _ _ (λ x t' H' → variant-fmap pts f (k x) H') _ H

    consumeString : ∀ str str' A o → parserSpec prods A str o str' → length str' ≤ length str
    consumeString' : ∀ A str rhs (f : ⟦ rhs ∥ A ⟧ → ⟦ A ⟧) str' → prods ⊢ str ~ rhs => f , str' → length str' ≤ length str
    consumeString str str' A _ (Produce _ H) = consumeString' A str _ _ str' H
    consumeString' A str .Nil .(λ x → x) .str Done = ≤-refl
    consumeString' A .(_ :: _) .(Inl _ :: _) f str' (Next H) = ≤-step (consumeString' A _ _ f str' H)
    consumeString' A str .(Inr _ :: _) _ str' (Call H1 H2) = ≤-trans (consumeString' A _ _ _ str' H2) (consumeString str _ _ _ H1)

    map-snoc : ∀ {a b} {f : a -> b} x xs ys -> map f xs ++ (f x :: ys) == map f (xs ++ (x :: Nil)) ++ ys
    map-snoc x Nil ys = refl
    map-snoc {f = f} x (x' :: xs) ys = cong (f x' ::_) (map-snoc x xs ys)

    subst2 : ∀ {A} {B : A -> Set} (C : (x : A) -> B x -> Set) {x x' : A} {y : B x} (p : x == x') -> C x y -> C x' (subst B p y)
    subst2 C refl z = z

    nextNonterm : ∀ {A B Bs xs sem} -> prod A (map Inr Bs ++ (Inr B :: xs)) sem ∈ prods -> prod A (map Inr (Bs ++ (B :: Nil)) ++ xs) (subst (λ xs' -> ⟦ xs' ∥ A ⟧) (map-snoc B Bs xs) sem) ∈ prods
    nextNonterm {A} {B} {Bs} {xs} {sem} i = subst2 (λ xs' sem' → prod A xs' sem' ∈ prods) (map-snoc B Bs xs) i


    prodsVariant : {a : Set} → Nonterm → String → FreeParser prods a → String → Set
\end{code}
%endif

Our next goal is that |RecOrder| is a variant for |fromProds|, as abbreviated by the |prodsVariant| type.
We cannot follow the definitions of |fromProds| as closely as we did for the partial correctness proof;
instead we need a complicated case distinction to keep track of the left-recursive chain we have followed in the proof.
For this reason, we split the |parseStep| apart into two lemmas |parseStepAdv| and |parseStepRec|, both showing that |buildParser| maintains the variant.
We also use a |filterStep| lemma that calls the correct |parseStep| for each production in the nondeterministic choice.
\begin{code}
    prodsVariant = variant' (pts prods) (fromProds prods) (RecOrder prods)

    parseStepAdv : ∀ A xs str str' → length str' < length str →
      prodsVariant A str (buildParser (hidden(A = A)) xs) str'
    parseStepRec : ∀ A xs str str' → length str' ≤ length str →
      ∀ ys (hidden(sem)) -> prod A (map Inr ys ++ xs) sem ∈ prods →
      prodsVariant A str (buildParser (hidden(A = A)) xs) str'
    filterStep : ∀ prods' → ((Forall(x)) x ∈ prods' → x ∈ prods) →
      ∀ A str str' → length str' ≤ length str →
      prodsVariant A str
        (foldr (choice (hiddenInstance(∈Tail ∈Head))) (fail (hiddenInstance(∈Tail ∈Head))) (map fromProd (filterLHS A prods')))
      str'
\end{code}
In the |parseStepAdv|, we deal with the situation that the parser has already consumed at least one character since it was called.
This means we can repeatedly use the |Left| constructor of |RecOrder| to show the variant holds.
%if style == newcode
\begin{code}
    parseStepAdv A Nil str str' lt = tt
    parseStepAdv A (Inl x :: xs) str Nil lt = tt
    parseStepAdv A (Inl x :: xs) str (c :: str') lt with x ≟ c
    parseStepAdv A (Inl x :: xs) (_ :: _ :: str) (.x :: str') (s≤s (s≤s lt)) | yes refl
      = parseStepAdv A xs _ _ (s≤s (≤-step lt))
    ... | no ¬p = tt
    parseStepAdv A (Inr B :: xs) str str' lt
      = Left lt
      , λ o str'' H → variant-fmap (pts prods) (fromProds prods) (buildParser xs)
        (parseStepAdv A xs str str'' (≤-trans (s≤s (consumeString str' str'' B o H)) lt))
\end{code}
Here, the lemma |variant-fmap| states that the variant holds for a program of the form |S >>= (Pure ∘ f)| if it does for |S|, since the |Pure| part does not make any recursive calls;
the lemma |consumeString str' str'' B| states that the string |str''| is shorter than |str'| if |str''| is the left-over string after matching |str''| with non-terminal |B|.
%endif

In the |parseStepRec|, we deal with the situation that the parser has only encountered non-terminals in the current production.
This means that we can use the |Right| constructor of |RecOrder| to show the variant holds until we consume a character,
after which we call |parseStepAdv| to finish the proof.
%if style == newcode
\begin{code}
    parseStepRec A Nil str str' lt ys i = tt
    parseStepRec A (Inl x :: xs) str Nil lt ys i = tt
    parseStepRec A (Inl x :: xs) str (c :: str') lt ys i with x ≟ c
    parseStepRec A (Inl x :: xs) (_ :: str) (.x :: str') (s≤s lt) ys i | yes refl
      = parseStepAdv A xs _ _ (s≤s lt)
    ... | no ¬p = tt
    parseStepRec A (Inr B :: xs) str str' lt ys i
      = Right lt (record { rec = i })
      , λ o str'' H → variant-fmap (pts prods) (fromProds prods) (buildParser xs)
        (parseStepRec A xs str str'' (≤-trans (consumeString str' str'' B o H) lt)
        (ys ++ (B :: Nil)) (nextNonterm i))
\end{code}
Apart from the previous lemmas, we make use of |nextNonterm i|,
which states that the current production starts with the non-terminals |ys ++ (B :: Nil)|.
%endif

The lemma |filterStep| shows that the variant holds on all subsets of the production rules,
analogously to the |filterStep| of the partial correctness proof.
It calls |parseStepRec| since the parser only starts consuming characters after it selects a production rule.
\begin{code}
    filterStep Nil A str str' lt subset = tt
    filterStep (prod lhs rhs sem :: prods') subset A str str' lt with A ≟n lhs
    ... | yes refl
      = variant-fmap (pts prods) (fromProds prods) (buildParser rhs)
        (parseStepRec A rhs str str' lt Nil (subset ∈Head))
        , filterStep prods' (subset ∘ ∈Tail) A str str' lt
    ... | no ¬p = filterStep prods' (subset ∘ ∈Tail) A str str' lt
\end{code}
As for partial correctness, we obtain the proof of termination by applying |filterStep| to the subset of |prods| consisting of |prods| itself.

\fi

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End:

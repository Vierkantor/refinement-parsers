\documentclass{eptcs}

\usepackage[style=alphabetic,natbib=true]{biblatex}
\addbibresource{handlers.bib}

%include agda.fmt
%include refinement-parsers.fmt

%include preamble.tex

%if style == newcode
\begin{code}
{-# OPTIONS --type-in-type #-}
open import Prelude

open import Axiom.Extensionality.Propositional
open import Level
postulate extensionality : Extensionality zero zero

_⊆_ : {a : Set} -> (P Q : a -> Set) -> Set
P ⊆ Q = ∀ x -> P x -> Q x
\end{code}
%endif

\begin{document}

\title{A predicate transformer semantics of parser combinators}
\def\titlerunning{A predicate transformer semantics of parser combinators}
\def\authorrunning{Tim Baanen and Wouter Swierstra}
% Of misschien iets als:
% A predicate transformer semantics for parsing
% Verifying parser combinators using predicate transformers
\author{Tim Baanen
  \institute{Vrije Universiteit Amsterdam}
    \and
    Wouter Swierstra
  \institute{Utrecht University}
  }    
%\email{\{t.baanen@@vu.nl,w.s.swierstra@@uu.nl\}}}
%
\maketitle              % typeset the header of the contribution

\section{Introduction}
\label{sec:intro}

There is a significant body of work on parsing using combinators
% TODO Check het paper van Nils anders danielsson voor een veeeel langere lijst
% met referenties over parser combinators
in functional programming languages~\cite{hutton, swierstra-duponcheel, list-of-successes,others?},. 
Yet how can we ensure that these parsers are correct? There is notably
less work that attempts to  answer this
question~\cite{total-parser-combinators, firsov-certification-context-free-grammars}.

Reasoning about such parser combinators is not at all trivial; they
use a variety of effects: state to store the string being parsed;
non-determinism to handle backtracking; and general recursion to deal
with recursive grammars. Proof techniques, such as equational
reasoning, that commonly used when reasoning about pure functional programs, are less
suitable when verifying effectful programs.%TODO Cite Fulgur and hutton? just do it?

In this paper, we explore a novel approach, drawing inspiration from
recent work on algebraic effects~\cite{eff, effect-handlers-in-scope,
  McBride-totally-free}.  
We demonstrate how to reason about all parsers uniformly using
\emph{predicate transformers}~\cite{pt-semantics-for-effects}.
We extend our previous work that uses predicate transformer semantics to reason about a single effect
to handle the combinations of effects used by parsers.
Our semantics is modular, allowing us to introduce concepts %TODO: wat bedoel je hier met concepts?
only when they are needed,
without having to rework the previous definitions.
In particular, our careful treatment
of general recursion lets us separate the partial correctness of the
combinators from their termination cleanly. Most existing
proofs require combinators to guarantee that the string being parsed
decreases, conflating termination and correctness.

In particular, this paper makes the following novel contributions:
\begin{itemize}
\item The non-recursive fragment of regular expressions can be correctly parsed
  using non-determinism (Section \ref{sec:regex-nondet});
  by combining non-determinism with general recursion (Section \ref{sec:combinations}),
  support for the Kleene star can be added without compromising our previous definitions
  (Section \ref{sec:regex-rec}). Although the resulting parser is not guaranteed to terminate,
  it is \emph{refined} by another implementation using Brzozowski derivatives that does terminate
  (Section \ref{sec:dmatch}).
  
\item Next, we show how this approach may be extended to handle
  context-free languages. To do so, we show how to write parsers using
  algebraic effects (Section \ref{sec:parser}), and map grammars to parsers (Section
  \ref{sec:fromProductions}). Once again, we can cleanly separate the proofs of partial
  correctness (Section \ref{sec:partialCorrectness}) and termination (Section \ref{sec:fromProds-terminates}).
\end{itemize}

All the programs and proofs in this paper are written in the dependently typed language Agda~\cite{agda-thesis}.
%TODO link?

\section{Recap: algebraic effects and predicate transformers}
Algebraic effects separate the \emph{syntax} and \emph{semantics} of
effectful operations. In this paper, we will model the by taking the
free monad over a given signature, describing certain
operations. The type of such a signature is defined as follows:
\begin{code}
record Sig : Set where
  constructor mkSig
  field
    C : Set
    R : C -> Set
\end{code}
Here the type |C| contains the `commands', or effectful operations
that a given effect supports. For each command |c : C|, the type |R c|
describes the possible responses.
The structure on a signature is that of a \emph{container}~\cite{categories-of-containers}.
For example, the following signature describes two operations: the
non-deterministic choice between two values, |Choice|; and a failure
operator, |Fail|.
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
This gives a monad, with the bind operator defined as follows:
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
  fail = Op Fail λ ()
  choice : (Forall(a)) Free Nondet a -> Free Nondet a -> Free Nondet a
  choice S₁ S₂ = Op Choice λ b -> if b then S₁ else S₂
\end{code}
In this paper, we will assign \emph{semantics} to effectful programs
by mapping them to \emph{predicate transformers}.
Each semantics will be computed by a fold over the free monad, mapping
some predicate |P : a -> Set| to a predicate on the result of the free
monad to a predicate of the entire computation of type |Free (eff C R) a -> Set|.
\begin{code}
  (wp) : (implicit(C : Set)) (implicit(R : C -> Set)) (implicit(a : Set)) ((c : C) -> (R c -> Set) -> Set) ->
    Free (mkSig C R) a -> (a -> Set) -> Set
  (wp alg (Pure x)) P  = P x
  (wp alg (Op c k)) P  = alg c λ x -> (wp (alg) (k x)) P
\end{code}
The \emph{predicate transformer} nature of these semantics
becomes evident when we assume the type of responses |R| does not depend on the command |c : C|.
The type of |alg : (c : C) → (R c → Set) → Set| then becomes |C → (R → Set) → Set|,
which is isomorphic to |(R → Set) → (C → Set)|.
Thus, |alg| has the form of a predicate transformer from postconditions of type
|R → Set| into preconditions of type |C → Set|.
% The type of |(wp alg)| under the same isomorphism becomes
% |(a -> Set) -> (Free e a → Set)|.
Two considerations cause us to define the types |alg : (c : C) → (R c → Set) → Set|,
and analogously |(wp alg) : Free (mkSig C R) a → (a → Set) → Set|.
By having the command as first argument to |alg|, we allow |R| to depend on |C|.
Moreover, |(wp alg)| computes semantics,
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

%if style == newcode
\begin{code}
module NoCombination2 where
  open NoCombination
  open Nondet
\end{code}
%endif
\begin{code}
  (wpNondetAll) : (Forall(a)) Free Nondet a -> (a -> Set) -> Set
  wpNondetAll S = wp ptAll S
\end{code}

Predicate transformers provide a single semantic domain to relate
programs and specifications. %cite refinement calculus?
Throughout this paper, we will consider specifications consisting of a
pre- and postcondition:
\begin{code}
module Spec where
  record Spec (a : Set) : Set where
    constructor [[_,_]]
    field
      pre : Set
      post : a -> Set
\end{code}
Inspired by work on the refinement calculus, we can assign a predicate
transformer semantics to specifications as follows:
\begin{code}    
  (wpSpec) : (Forall(a)) Spec a -> (a -> Set) -> Set
  wpSpec [[ pre , post ]] P = pre ∧ (∀ o -> post o -> P o)
\end{code}
This computes the `weakest precondition' necessary for a specification
to imply that the desired postcondition |P| holds. In particular, the
precondition |pre| should hold and any possible result satisfying the
postcondition |post| should imply the postcondition |P|.

Finally, we use the \emph{refinement relation} to compare programs and specifications:
\begin{code}
  _⊑_ : (Forall(a : Set)) (pt1 pt2 : (a -> Set) -> Set) -> Set
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
To illustrate how to reason about non-deterministic code, we begin by
defining a regular expression matcher. Initially, we will restrict
ourselves to non-recursive regular expressions; we will add recursion
in the next section.

We begin by defining the |Regex| datatype for regular expressions as
follows: An element of this type represents the syntax of a regular
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
Note that the |Empty| regular expression corresponds to the empty
language, while the |Epsilon| expression only matches the empty
string. Furthermore, our language for regular expressions is closed
under choice (|_∣_|), concatenation (|_·_|) and linear repetition
denoted by the Kleene star (|_*|).

What should our regular expression matcher return?  A Boolean value is
not particularly informative; yet we also choose not to provide an
intrinsically correct definition, instead performing extrensic
verification using our predicate transformer semantics. The |tree|
data type below, captures a potential parse tree associated with a
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
  Concat      : (implicit(l r : Regex)) (implicit(ys zs : String)) (implicit(y : tree l)) (implicit(z : tree r))     Match l ys y -> Match r zs z ->
                                                                                                                     Match (l · r) (ys ++ zs) (y , z)
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
the concatenation of the strings |xs| and |zs| -- although there may
be many possible ways to decompose a string into two
substrings. Finally, the two constructors for the Kleene star, |r ⋆|
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
  open NoCombination2
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
  match (Singleton c)  (.c :: Nil)    | yes refl  = Pure c
  match (Singleton c)  (x :: Nil)     | no ¬p     = fail
  match (Singleton c)  (_ :: _ :: _)  = fail
  match (l ∣ r)        xs             = choice (Inl <$> match l xs) (Inr <$> match r xs)  
  match (l · r)        xs             = do
    (ys , zs) <- allSplits xs
    y <- match l ys
    z <- match r zs
    Pure (y , z)
  match (r *) xs = fail    
  \end{code}
  \caption{The definition of the |match| function}
  \label{fig:match}
\end{figure}  
Finally, we cannot yet handle the case for the Kleene star.  We could
attempt to mimick the case for concatenation, attempting to match |r ·
(r ⋆)|. This definition, however, is rejected by Agda as it is not
structurally recursive. For now, however, we choose to simply fail on
all such regular expressions.

Still, we can prove that the |match| function behaves correctly on all
regular expressions that do not contain iteration. The |hasNo*|
predicate holds of all such iteration-free regular expressions:
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
  matchSound : ∀ r xs -> (wpSpec [[ (pre r xs) , (post r xs) ]]) ⊑ (wpNondetAll (match r xs))
\end{code}
This lemma guarantees that all the parse trees computed by the |match|
function satisfy the |Match| relation, provided the input regular
expression does not contain iteration. Although we have omitted the
proof, we will sketch the key lemmas and definitions that are
necessary to complete it.

First of all, we quickly run into problems as soon as we need to
reason about programs composed using the monadic bind operator. In
particular, when verifying the case for |l · r|, we would like to use
our induction hypotheses on two recursive calls. To do, we prove the
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

The correctness proof for |match| closely matches the structure of |match| (and by extension |allSplits|).
It uses the same recursion on |Regex| as in the definition of |match|.
Since we make use of |allSplits| in the definition, we first give its correctness proof.
\begin{code}
  allSplitsPost : String → String × String → Set
  allSplitsPost xs (ys , zs) = xs == ys ++ zs
  allSplitsSound : ∀ xs -> (wpSpec [[ ⊤ , (allSplitsPost xs) ]]) ⊑ (wpNondetAll (allSplits xs))
\end{code}
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
The matcher we have defined in the previous section is unfinished,
since it is not able to handle regular expressions that incorporate the Kleene star.
The fundamental issue is that the Kleene star allows for arbitrarily many distinct matchings in certain cases.
For example, matching |Epsilon *| with the empty string |""| will allow for repeating the |Epsilon| arbitrarily often, since |Epsilon · (Epsilon *)| is equivalent to both |Epsilon| and |Epsilon *|.
Thus, we cannot implement |match| on the |_*| operator in the naïve way.

What we will do instead is to deal with the recursion as an effect.
A recursively defined (dependent) function of type |(i : I) -> O i|
can instead be given as an element of the type |(i : I) -> Free (Rec I O) (O i)|,
where |Rec I O| is the signature of \emph{general recursion}~\cite{McBride-totally-free}:
\begin{code}
Rec : (I : Set) (O : I -> Set) -> Sig
Rec I O = mkSig I O
\end{code}

Defining |match| in the |Free (Rec _ _)| monad is not sufficient to implement it fully either,
since replacing the effect |Nondet| with |Rec| does not allow for nondeterminism anymore.
While the Kleene star might work, the other parts of |match| do not work anymore.
We need a way to combine effects.

We can combine two effects in a straightforward way: given signatures |mkSig C₁ R₁| and |mkSig C₂ R₂|,
we can define a combined signature by taking the disjoint union of the commands and responses,
resulting in |mkSig (Either C₁ C₂) [ R₁ , R₂ ]|,
where |[ R₁ , R₂ ]| is the unique map given by applying |R₁| to values in |C₁| and |R₂| on |C₂|~\cite{effect-handlers-in-scope}.
If we want to support more effects, we can repeat this process of disjoint unions,
but this quickly becomes somewhat cumbersome.
For example, the disjount union construction is associative semantically, but not syntactically.
If two programs have the same set of effects that is associated differently, we cannot directly compose them.

Instead of building a new effect type, we modify the |Free| monad to take a list of signatures instead of a single signature.
The |Pure| constructor remains as it is,
while the |Op| constructor additionally takes an index into the list to specify which effect is invoked.
%if style == newcode
\begin{code}
module Combinations where
  open Sig
  open AlmostRegex using (allSplitsPost)
\end{code}
%endif
\begin{code}
  data Free (es : List Sig) (a : Set) : Set where
    Pure : a -> Free es a
    Op : (hidden(e : Sig)) (i : e ∈ es) (c : C e) (k : R e c -> Free es a) -> Free es a
\end{code}
By using a list of effects instead of allowing arbitrary disjoint unions,
we have effectively chosen that the disjoint unions canonically associate to the right.
Since the disjoint union is also commutative,
it would be cleaner to have the collection of effects be unordered as well.
Unfortunately, Agda does not provide a multiset type that is easy to work with.

We choose to use the same names and almost the same syntax for this new definition of |Free|,
since all definitions that use the old version can be ported over with almost no change.
Thus, we will not repeat definitions such as |_>>=_| and |consequence| for the new |Free| type.
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

Most of this bookkeeping can be inferred by Agda's typeclass inference,
so we make the indices instance arguments,
indicated by the double curly braces |⦃ ⦄| surrounding the arguments.
\begin{code}
  fail : (Forall(a es)) ⦃ iND : Nondet ∈ es ⦄ -> Free es a
  fail ⦃ iND ⦄ = Op iND Fail λ ()
  choice : (Forall(a es)) ⦃ iND : Nondet ∈ es ⦄ -> Free es a -> Free es a -> Free es a
  choice ⦃ iND ⦄ S₁ S₂ = Op iND Choice λ b -> if b then S₁ else S₂

  call : (Forall(I O es)) ⦃ iRec : Rec I O ∈ es ⦄ -> (i : I) -> Free es (O i)
  call ⦃ iRec ⦄ i = Op iRec i Pure
\end{code}
%if style == newcode
\begin{code}
  choices : ∀ {es a} ⦃ iND : Nondet ∈ es ⦄ → List (Free es a) → Free es a
  choices ⦃ iND ⦄ = foldr choice fail
\end{code}
%endif
For convenience of notation, we introduce the |(RecArr _ es _)| notation for general recursion,
i.e. Kleisli arrows into |Free (Rec _ _ :: es)|.
\begin{code}
  RecArr' : (C : Set) (es : List Sig) (R : C → Set) → Set
  (RecArr C es R) = (c : C) -> Free (mkSig C R :: es) (R c)
\end{code}
%if style == newcode
\begin{code}
instance
  inHead : ∀ {a} {x : a} {xs : List a} → x ∈ (x :: xs)
  inHead = ∈Head
  inTail : ∀ {a} {x x' : a} {xs : List a} → ⦃ i : x ∈ xs ⦄ → x ∈ (x' :: xs)
  inTail ⦃ i ⦄ = ∈Tail i
\end{code}
%endif

With the syntax for combinations of effects defined, let us turn to semantics.
Since the weakest precondition predicate transformer for a single effect is given as a fold
over the effect's predicate transformer,
the semantics for a combination of effects can be given as a fold over a (dependent) list of predicate transformers.
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
  record PT (e : Sig) : Set where
    constructor mkPT
    field
      pt : (c : C e) → (R e c → Set) → Set
      mono : ∀ c P P' → P ⊆ P' → pt c P → pt c P'

  data PTs : List Sig -> Set where
    Nil : PTs Nil
    _::_ : (Forall(e es)) PT e -> PTs es -> PTs (e :: es)
\end{code}
The record type |PT| not only contains a predicate transformer |pt|,
but also a proof that |pt| is monotone in its predicate.
The requirement of monotonicity is needed to prove the lemma |terminates-fmap| we introduce later,
and makes intuitive sense: if the precondition holds for a certain postcondition,
a weaker postcondition should also have its precondition hold.

Given a such a list of predicate transformers,
defining the semantics of an effectful program is a straightforward generalization of the previously defined semantics |wp|.
The |Pure| case is identical, and in the |Op| case we can apply the predicate transformer returned by the |lookupPT| helper function.
\begin{code}
  lookupPT : (Forall(C R es)) (pts : PTs es) (i : mkSig C R ∈ es) ->
    (c : C) -> (R c -> Set) -> Set
  lookupPT (pt :: pts) ∈Head = PT.pt pt
  lookupPT (pt :: pts) (∈Tail i) = lookupPT pts i
\end{code}
%if style == newcode
\begin{code}
  lookupMono : ∀ {C R es} (pts : PTs es) (i : mkSig C R ∈ es) -> ∀ c P P' → P ⊆ P' → lookupPT pts i c P → lookupPT pts i c P'
  lookupMono (pt :: pts) ∈Head = PT.mono pt
  lookupMono (pt :: pts) (∈Tail i) = lookupMono pts i
\end{code}
%endif
This results in the following definition of the semantics for combinations of effects.
\begin{code}
  (wp) : (Forall(a es)) (pts : PTs es) -> Free es a -> (a -> Set) -> Set
  (wp pts (Pure x)) P = P x
  (wp pts (Op i c k)) P = lookupPT pts i c λ x -> (wp pts (k x)) P
\end{code}

The effects we are planning to use for |match| are a combination of nondeterminism and general recursion.
We re-use the |ptAll| semantics of nondeterminism, packaging them in a |PT| record.
However, it is not as easy to give a predicate transformer for general recursion,
since the intended semantics of a recursive call depend
on the function that is being called, i.e. the function that is being defined.

As long as we have a specification of a function of type |(i : I) -> O i|,
for example in terms of a relation of type |(i : I) -> O i -> Set|,
we are able to define a predicate transformer:
\begin{code}
  ptRec : (Forall(I O)) ((i : I) -> O i -> Set) -> PT (Rec I O)
  PT.pt (ptRec R) i P = ∀ o -> R i o -> P o
  PT.mono (ptRec R) c P P' imp asm o h = imp _ (asm _ h)
\end{code}
In the case of verifying the |match| function, the |Match| relation will play the role of |R|.
If we use |ptRec R| as a predicate transformer to check that a recursive function satisfies the relation |R|,
then we are proving \emph{partial correctness}, since we assume each recursive call succesfully returns
a correct value according to the relation |R|.

\section{Recursively parsing every regular expression} \label{sec:regex-rec}

To deal with the Kleene star, we rewrite |match| as a generally recursive function using a combination of effects.
Since |match| makes use of |allSplits|, we also rewrite that function to use a combination of effects.
The types become:
\begin{code}
  allSplits : (Forall(a es)) ⦃ iND :  Nondet ∈ es ⦄ -> List a -> Free es (List a × List a)
  match : (Forall(es)) ⦃ iND : Nondet ∈ es ⦄ → (RecArr (Regex × String) es (tree ∘ Pair.fst))
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
the only change in the definition of |match| and |allSplits| will be that |match| now implements the Kleene star:
\begin{code}
  match ((r *) , Nil) = Pure Nil
  match ((r *) , xs@(_ :: _)) = do
    (y , ys) <- call (hiddenInstance(∈Head)) ((r · (r *)) , xs)
    Pure (y :: ys)
\end{code}

The effects we need to use for running |match| are a combination of nondeterminism and general recursion.
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

  (wpMatch) : (Forall(a)) Free (Rec (Pair Regex String) (tree ∘ Pair.fst) :: Nondet :: Nil) a ->
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

We can reuse exactly the same proof to show |allSplits| is correct,
since we use the same semantics for the effects in |allSplits|.
Similarly, the correctness proof of |match| will be the same on all cases except the Kleene star.
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
  matchSound ((r *) , Nil)        P (preH , postH) = postH _ StarNil
  matchSound ((r *) , (x :: xs))  P (preH , postH) o H = postH _ (StarConcat H)
\end{code}

At this point, we have defined a parser for regular languages
and formally proved that its output is always correct.
However, |match| does not necessarily terminate:
if |r| is a regular expression that accepts the empty string,
then calling |match| on |r *| and a string |xs|
results in the first nondeterministic alternative being an infinitely deep recursion.

The next step is then to write a parser that always terminates
and show that |match| is refined by it.
Our approach is to do recursion on the input string
instead of on the regular expression.

\section{Termination, using derivatives} \label{sec:dmatch}
Since recursion on the structure of a regular expression
does not guarantee termination of the parser,
we can instead perform recursion on the string to be parsed.
To do this, we make use of an operation on languages called the Brzozowski derivative.
\begin{Def}[\cite{Brzozowski}]
The \emph{Brzozowski derivative} of a formal language |L| with respect to a character |x| consists of all strings |xs| such that |x :: xs ∈ L|.
\end{Def}

Importantly, if |L| is regular, so are all its derivatives.
Thus, let |r| be a regular expression, and |d r /d x| an expression for the derivative with respect to |x|,
then |r| matches a string |x :: xs| if and only if |d r /d x| matches |xs|.
This suggests the following implementation of matching an expression |r| with a string |xs|:
if |xs| is empty, check whether |r| matches the empty string;
otherwise let |x| be the head of the string and |xs'| the tail and go in recursion on matching |d r /d x| with |xs'|.

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

  matchEpsilon Empty = no λ ()
  matchEpsilon Epsilon = yes (tt , Epsilon)
  matchEpsilon (Singleton x) = no λ ()
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
The definitions of |matchEpsilon| is given by structural recursion on the regular expression, just as the derivative operator is:
\begin{code}
  d_/d_ : Regex -> Char -> Regex
  d Empty /d c = Empty
  d Epsilon /d c = Empty
  d Singleton x /d c with c ≟ x
  ... | yes p = Epsilon
  ... | no ¬p = Empty
  d l · r /d c with matchEpsilon l
  ... | yes p = ((d l /d c) · r) ∣ (d r /d c)
  ... | no ¬p = (d l /d c) · r
  d l ∣ r /d c = (d l /d c) ∣ (d r /d c)
  d r * /d c = (d r /d c) · (r *)
\end{code}

In order to use the derivative of |r| to compute a parse tree for |r|,
we need to be able to convert a tree for |d r /d x| to a tree for |r|.
We do this with the function |integralTree|:
\begin{code}
  integralTree : (implicit(x : Char)) (r : Regex) -> tree (d r /d x) → tree r
\end{code}
We can also define it with exactly the same case distinction as we used to define |d_/d_|.
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

The code for the parser, |dmatch|, itself is very short.
As we sketched, for an empty string we check that the expression matches the empty string,
while for a non-empty string we use the derivative to perform a recursive call.
\begin{code}
  dmatch : (Forall(es)) ⦃ iND : Nondet ∈ es ⦄ -> (RecArr (Regex × String) es (tree ∘ Pair.fst))
  dmatch (r , Nil) with matchEpsilon r
  ... | yes (ms , _)  = Pure ms
  ... | no ¬p         = fail
  dmatch (r , (x :: xs)) = integralTree r <$> call (hiddenInstance(∈Head)) ((d r /d x) , xs)
\end{code}

Since |dmatch| always consumes a character before going in recursion, we can easily prove that each recursive call only leads to finitely many other calls.
This means that for each input value we can unfold the recursive step in the definition a bounded number of times and get a computation with no recursion.
Intuitively, this means that |dmatch| terminates on all input.
If we are going to give a formal proof of termination, we should first determine the correct formalization of this notion.
For that, we need to consider what it means to have no recursion in the unfolded computation.
A definition for the |while| loop using general recursion looks as follows:
\begin{code}
  while : (Forall(es a)) ⦃ iRec : Rec a (K a) ∈ es ⦄ ->
    (a -> Bool) -> (a -> a) -> (a -> Free es a)
  while cond body i = if cond i then Pure i else (call (body i))
\end{code}
We would like to say that some |while| loops terminate, yet the definition of |while| always contains a |call| in it.
Thus, the requirement should not be that there are no more calls left,
but that these calls are irrelevant.

Intuitively, we could say that a definition |S| calling |f| terminates
if we make the unfolded definition into a |Partial| computation by replacing |call| with |fail|,
the definition terminates if the |Partial| computation still works the same, i.e. it refines |S|.
However, this mixes the concepts of correctness and termination.
We want to see that the |Partial| computation gives some output, without caring about which output this is.
Thus, we should only have a trivial postcondition.
We formalize this idea in the |terminates-in| predicate.
\begin{code}
  terminates-in : (Forall(C R es a)) (pts : PTs es)
    (f : (RecArr C es R)) (S : Free (mkSig C R :: es) a) → Nat → Set
  terminates-in pts f (Pure x) n = ⊤
  terminates-in pts f (Op ∈Head c k) Zero = ⊥
  terminates-in pts f (Op ∈Head c k) (Succ n) =
    terminates-in pts f (f c >>= k) n
  terminates-in pts f (Op (∈Tail i) c k) n =
    lookupPT pts i c (λ x → terminates-in pts f (k x) n)
\end{code}

Since |dmatch| always consumes a character before going in recursion,
we can bound the number of recursive calls with the length of the input string.
The proof goes by induction on this string.
Unfolding the recursive |call| gives |integralTree <$> dmatch (d r /d x , xs)|,
which we rewrite using the associativity monad law in a lemma called |terminates-fmap|.
\begin{code}
  dmatchTerminates : (r : Regex) (xs : String) →
    terminates-in (ptAll :: Nil) (dmatch (hiddenInstance(∈Head)) ) (dmatch (hiddenInstance(∈Head)) (r , xs)) (length xs)
  dmatchTerminates r Nil with matchEpsilon r
  dmatchTerminates r Nil | yes p = tt
  dmatchTerminates r Nil | no ¬p = tt
  dmatchTerminates r (x :: xs) = terminates-fmap (length xs)
    (dmatch (hiddenInstance(∈Head)) ((d r /d x) , xs))
    (dmatchTerminates (d r /d x) xs)
\end{code}
%if style == newcode
\begin{code}
    where
    assoc : ∀ {es a b c} (S : Free es a) (f : a → Free es b) (g : b → Free es c) → (S >>= f) >>= g == S >>= (λ x → f x >>= g)
    assoc (Pure x) f g = refl
    assoc (Op i c k) f g = cong (Op i c) (extensionality λ x → assoc (k x) f g)
    terminates-fmap : ∀ {C R es a b pts f} {g : a → b} n (S : Free (mkSig C R :: es) a) → terminates-in pts f S n → terminates-in pts f (S >>= (Pure ∘ g)) n
    terminates-fmap n (Pure x) H = H
    terminates-fmap {pts = pts} {f} {g} (Succ n) (Op ∈Head c k) H = subst (λ S → terminates-in pts f S n) (assoc (f c) k (Pure ∘ g)) (terminates-fmap n (f c >>= k) H)
    terminates-fmap {pts = pts} n (Op (∈Tail i) c k) H = lookupMono pts i c _ _ (λ x → terminates-fmap n (k x)) H
\end{code}
%endif

To show partial correctness of |dmatch|,
we can use the transitivity of the refinement relation.
If we apply transitivity, it suffices to show that |dmatch| is a refinement of |match|.
Our first step is to show that the derivative operator is correct,
i.e. |d r /d x| matches those strings |xs| such that |r| matches |x :: xs|.
\begin{code}
  derivativeCorrect : (Forall(x xs)) ∀ r -> (Forall(y))
    Match (d r /d x) xs y -> Match r (x :: xs) (integralTree r y)
\end{code}
The proof mirrors the definitions of these functions,
being structured as a case distinction on the regular expression.
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

Before we can prove the correctness of |dmatch| in terms of |match|, it turns
out that we also need to describe |match| itself better. The meaning of our
goal, to show that |match| is refined by |dmatch|, is to prove that the output
of |dmatch| is a subset of that of |match|. Since |match| makes use of
|allSplits|, we first prove that all splittings of a string |xs| are in the
output of |allSplits xs|. This following lemma and |allSplitsSound| together
show that calling |allSplits xs| is equivalent, under the semantics |wpMatch|, to its
specification |[[ ⊤ , allSplitsPost xs ]]|.
\begin{code}
  allSplitsComplete : (xs : String) → (wpMatch (allSplits (hiddenInstance(∈Tail ∈Head)) xs)) ⊑ (wpSpec [[ ⊤ , allSplitsPost xs ]])
\end{code}
%if style == newcode
\begin{code}
  allSplitsComplete Nil P H = tt , λ
    { (Nil , .Nil) refl → H }
  allSplitsComplete (x :: xs) P H = tt , λ
    { (Nil , .(x :: xs)) refl → Pair.fst H
    ; ((.x :: ys) , zs) refl → Pair.snd (allSplitsComplete xs (λ {(ys , zs) → P ((x :: ys) , zs)}) (wpFromBind (allSplits (ys ++ zs)) _ (Pair.snd H))) (ys , zs) refl}
\end{code}
%endif
The proof mirrors |allSplits|, performing induction on |xs|.

Using the preceding lemmas, we can prove the partial correctness of |dmatch| by showing it refines |match|:
% TODO make this wpMatch dmatch ⊑ wpSpec matchSpec ?
\begin{code}
  dmatchSound : ∀ r xs -> (wpMatch (match (hiddenInstance(∈Head)) (r , xs))) ⊑ (wpMatch (dmatch (hiddenInstance(∈Head)) (r , xs)))
\end{code}
Since we need to perform the case distinctions of |match| and of |dmatch|,
the proof is longer than that of |matchSoundness|.
Despite the length, most of it consists of performing the case distinction,
then giving a simple argument for each case.
Therefore, we omit the proof.
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

With the proof of |dmatchSound| finished, we can conclude that |dmatch| always returns a correct parse tree, i.e. that |dmatch| is sound.
However, |dmatch| is \emph{not} complete with respect to the |Match| relation:
since |dmatch| never makes a nondeterministic choice, it will not return all possible parse trees as specified by |Match|,
only the first tree that it encounters.
Still, we can express the property that |dmatch| finds a parse tree if it exists.
In other words, we will show that if there is a valid parse tree, |dmatch| returns any parse tree (and this is a valid tree by |dmatchSound|).
To express that |dmatch| returns something, we use a trivially true postcondition,
and replace the demonic choice of the |ptAll| semantics with the angelic choice of |ptAny|:
\begin{code}
  dmatchComplete : ∀ r xs y → Match r xs y →
    (wp (ptRec matchSpec :: ptAny :: Nil) (dmatch (hiddenInstance(∈Head)) (r , xs))) (λ _ → ⊤)
\end{code}
The proof is short, since |dmatch| can only |fail| when it encounters an empty string and a regex that does not match the empty string, contradicting the assumption immediately:
\begin{code}
  dmatchComplete r Nil y H with matchEpsilon r
  ... | yes p = tt
  ... | no ¬p = ¬p (_ , H)
  dmatchComplete r (x :: xs) y H y' H' = tt
\end{code}
Note that |dmatchComplete| does not show that |dmatch| terminates:
the semantics for the recursive case assume that |dmatch| always returns some value |y'|.

In the proofs of |dmatchSound| and |dmatchComplete|, we demonstrate the power of predicate transformer semantics for effects:
by separating syntax and semantics, we can easily describe different aspects (soundness and completeness) of the one definition of |dmatch|.
Since the soundness and completeness result we have proved imply partial correctness, and partial correctness and termination imply total correctness,
we can conclude that |dmatch| is a totally correct parser for regular languages.

Note the correspondences of this section with a Functional Pearl by \citet{harper-regex},
which also uses the parsing of regular languages as an example of principles of functional software development.
Starting out with defining regular expressions as a data type and the language associated with each expression as an inductive relation,
both use the relation to implement essentially the same |match| function, which does not terminate.
In both, the partial correctness proof of |match| uses a specification expressed as a postcondition,
based on the inductive relation representing the language of a given regular expression.
Where we use nondeterminism to handle the concatenation operator,
\citeauthor{harper-regex} uses a continuation-passing parser for control flow.
Since the continuations take the unparsed remainder of the string,
they correspond almost directly to the |Parser| effect of the following section.
Another main difference between our implementation and \citeauthor{harper-regex}'s
is in the way the non-termination of |match| is resolved.
\citeauthor{harper-regex} uses the derivative operator to rewrite the expression in a standard form
which ensures that the |match| function terminates.
We use the derivative operator to implement a different matcher |dmatch| which is easily proved to be terminating,
then show that |match|, which we have already proven partially correct, is refined by |dmatch|.
The final major difference is that \citeauthor{harper-regex} uses manual verification of the program and our work is formally computer-verified.
Although our development takes more work, the correctness proofs give more certainty than the informal arguments made by \citeauthor{harper-regex}.
In general, choosing between informal reasoning and formal verification will always be a trade-off between speed and accuracy.

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
  record PTS (s : Set) (e : Sig) : Set where
    constructor mkPTS
    field
      pt : (c : C e) → (R e c → s → Set) → s → Set
      mono : ∀ c P P' → (∀ x t → P x t → P' x t) → pt c P ⊆ pt c P'
\end{code}
%if style == newcode
\begin{code}
  data PTSs (s : Set) : List Sig -> Set where
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
we have fond a predicate transformer semantics that incorporates the current state:
\begin{code}
  (wpS) : (Forall(s es a)) (pts : PTSs s es) -> Free es a -> (a -> s -> Set) -> s -> Set
  (wpS pts (Pure x)) P = P x
  (wpS pts (Op i c k)) P = lookupPTS pts i c λ x -> (wpS pts (k x)) P
\end{code}

In this definition for |wpS|, we assume that all effects share access to one mutable variable of type |s|.
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
  empty? : (Forall(a)) List a -> Set
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
Following their development, we parametrize our definitions over a collection of nonterminal symbols.
%if style == newcode
\begin{code}
open import Relation.Binary
\end{code}
%endif
\begin{code}
record GrammarSymbols : Set where
  field
    Nonterm : Set
    ⟦_⟧ : Nonterm -> Set
    _≟n_ : Decidable {A = Nonterm} _==_
\end{code}
The elements of the type |Char| are the \emph{terminal} symbols.
The elements of the type |Nonterm| are the \emph{nonterminal} symbols, representing the language constructs.
As for |Char|, we also need to be able to decide the equality of nonterminals.
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
For each nonterminal |A|, our goal is to parse a string into a value of type |⟦ A ⟧|,
based on a set of production rules.
A production rule $A \to xs$ gives a way to expand the nonterminal |A| into a list of symbols |xs|,
such that successfully matching each symbol of |xs| with parts of a string
gives a match of the string with |A|.
Since matching a nonterminal symbol |B| with a (part of a) string results in a value of type |⟦ B ⟧|,
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
The main function is |fromProds|: given a nonterminal,
it selects the productions with this nonterminal on the left hand side using |filterLHS|,
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
and making a recursive |call| to |fromProds| for each nonterminal symbol.
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
the production rules, an input string, a nonterminal, the output of the parser, and the remaining unparsed string.
Due to the many arguments, the notation is unfortunately somewhat unwieldy.
To make it a bit easier to read, we define two relations in mutual recursion,
one for all productions of a nonterminal,
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

  record StateSpec (s a : Set) : Set where
    constructor [[_,_]]
    field
      pre : s -> Set
      post : s -> a -> s -> Set

  wpSpec : {s a : Set} -> StateSpec s a -> (a -> s -> Set) -> s -> Set
  wpSpec [[ pre , post ]] P t = pre t ∧ (∀ o t' -> post t o t' -> P o t')

  _⊑_ : {s a : Set} (pt1 pt2 : (a -> s -> Set) -> s -> Set) -> Set
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
Thus, we parametrise |filterStep| by a list |prods'| and a proof that it is a sublist of |prods|.
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
since we are able to call the same nonterminal repeatedly,
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
Since the position in the string and current nonterminal together fully determine the state of |fromParsers|,
it will not terminate.
We need to ensure that the grammars passed to the parser do not allow for such loops.

Intuitively, the condition on the grammars should be that they are not \emph{left-recursive},
since in that case, the parser should always advance its position in the string before it encounters the same nonterminal.
This means that the number of recursive calls to |fromProds| is bounded
by the length of the string times the number of different nonterminals occurring in the production rules.
The type we will use to describe the predicate ``there is no left recursion'' is constructively somewhat stronger:
we define a left-recursion chain from $A$ to $B$ to be
a sequence of nonterminals $A, \dots, A_i, A_{i+1}, \dots, B$,
such that for each adjacent pair $A_i, A_{i+1}$ in the chain, there is a production of the form $A_{i+1} \to B_1 B_2 \dots B_n A_i \dots$, where $B_1 \dots B_n$ are all nonterminals.
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
  record Termination (hidden(s es C R)) (pts : PTSs s (mkSig C R :: es)) (f : (RecArr C es R)) : Set where
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
we need to show that there is no infinite descending chain starting from some nonterminal |A| and string |str|.
The proof is based on iteration on two natural numbers |n| and |k|,
which form an upper bound on the number of allowed left-recursive calls in sequence and unconsumed characters in the string respectively.
Note that the number |bound| is an upper bound for |n| and the length of the input string is an upper bound for |k|.
Since each nonterminal in the production will decrease |n| and each terminal will decrease |k|,
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
the lemma |consumeString str' str'' B| states that the string |str''| is shorter than |str'| if |str''| is the left-over string after matching |str''| with nonterminal |B|.
%endif

In the |parseStepRec|, we deal with the situation that the parser has only encountered nonterminals in the current production.
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
which states that the current production starts with the nonterminals |ys ++ (B :: Nil)|.
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

\section{Discussion}

In this paper, we have described a representation of parsers and shown how to perform verification of parsers in this representation.
We will discuss how our work relates to other parser verifications.
Our sections on regular expressions have a similar structure to a Functional Pearl by \citet{harper-regex}.
The main difference is that our work is based on formal verification using Agda,
while \citeauthor{harper-regex} uses manual and informal reasoning.
The sections on context-free grammars could be compared to work by \citet{total-parser-combinators, firsov-certification-context-free-grammars}.
Here the difference, apart from a different parsing algorithm, can be found in how (non)termination is dealt with.
We opt for a strong separation of syntax and semantics,
using the |Rec| effect to give the syntax of programs regardless of termination,
later proving the semantic property of termination.
In contrast, \citeauthor{total-parser-combinators, firsov-certification-context-free-grammars}
deal with termination syntactically, either by incorporating delay and force operators in the grammar,
or explicitly passing around a proof of termination in the definition of the parser.

A different representation of languages used in verification is the \emph{coinductive trie}~\cite{coinductive-trie}.
The approach of \citeauthor{coinductive-trie} is in the opposite direction to ours:
in order to verify constructions on automata, the language they accept is mapped to a trie,
then this trie is compared to the trie that we get by applying the corresponding constructions on tries.
Similarly, \citet{ooagda} use a coinductive type to represent effectful programs with arbitrarily large input.
These two coinductive constructions carry proofs of productivity, in the form of sized types, in their definitions,
again mixing syntax and semantics.
% perhaps also Validating LR(1) Parsers https://link.springer.com/chapter/10.1007/978-3-642-28869-2_20

In conclusion, the two distinguishing features of our work are formality and modularity.
We could introduce the combination of effects, petrol-driven termination, semantics for state and variant-based termination
without impacting existing definitions.
We strictly separate the syntax and semantics of the programs,
and partial correctness from termination.
This results in verification proofs that do not need to carry around many goals,
allowing most of them to consist of unfolding the definition and filling in the obvious terms.

In the process of this verification, we have solved some open issues in the area of predicate transformer semantics and leave others open.
\citet{pt-semantics-for-effects} mention two avenues of further work that our work makes advances on: the semantics for combinations of effects
and the verification of non-trivial programs using algebraic effects.
Still, we chose to verify parsers with applying predicate transformers to them in the back of our mind,
so the goal of verifying a practical program remains a step further.
% Perhaps a translation of ``er valt iets af te dingen aan het idee dat we een praktisch programma verifiëren'' is more apt.

% TODO: discuss further work: (interaction of) handlers, efficiency, more?

We should also note that the engineering effort expected by \citeauthor{pt-semantics-for-effects} has not been needed for our paper.
The optimist can conclude that the elegance of our framework caused it to prevent the feared level of complication;
the pessimist can conclude that the real hard work will be required as soon as we encounter a real-world application.

\printbibliography
\end{document}

%%% Local Variables:
%%% mode: agda
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End: 



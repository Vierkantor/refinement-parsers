\documentclass[acmsmall, anonymous, review]{acmart}
\settopmatter{printfolios=true,printccs=false,printacmref=false}

%include agda.fmt
%include refinement-parsers.fmt

%include preamble.tex

%if style == newcode
\begin{code}
{-# OPTIONS --type-in-type #-}
open import Prelude

_⊆_ : {a : Set} -> (P Q : a -> Set) -> Set
P ⊆ Q = ∀ x -> P x -> Q x
\end{code}
%endif

\title{Verified parsers using the refinement calculus and algebraic effects}
\author{Tim Baanen \and Wouter Swierstra}

\begin{document}
\maketitle

There are various ways to write a parser in functional languages, for example using parser combinations.
How do we ensure these parsers are correct?
Previous work has shown that predicate transformers are useful for verification of programs using algebraic effects.
This paper will show how predicate transformers and algebraic effects allow for formal verification of parsers.

\section{Recap: algebraic effects and predicate transformers}
Algebraic effects were introduced to allow for incorporating side effects in functional languages.
For example, the effect |ENondet| allows for nondeterministic programs:
\begin{code}
record Effect : Set where
  constructor eff
  field
    C : Set
    R : C -> Set

data CNondet : Set where
  Fail : Set -> CNondet
  Split : CNondet
RNondet : CNondet -> Set
RNondet (Fail a) = a
RNondet Split = Bool

ENondet = eff CNondet RNondet
\end{code}

%if style == newcode
\begin{code}
module NoCombination where
\end{code}
%endif
We represent effectful programs using the |Free| datatype.
\begin{code}
  data Free (e : Effect) (a : Set) : Set where
    Pure : a -> Free e a
    Step : (c : Effect.C e) -> (Effect.R e c -> Free e a) -> Free e a
\end{code}
This gives a monad, with the bind operator defined as follows:
\begin{code}
  _>>=_ : ∀ {a b e} -> Free e a -> (a -> Free e b) -> Free e b
  Pure x >>= f = f x
  Step c k >>= f = Step c (λ x -> k x >>= f)
\end{code}

The easiest way to use effects is with smart constructors:
\begin{code}
  fail : ∀ {a} -> Free ENondet a
  fail {a} = Step (Fail a) Pure
  split : ∀ {a} -> Free ENondet a -> Free ENondet a -> Free ENondet a
  split S₁ S₂ = Step Split λ b -> if b then S₁ else S₂
\end{code}

To give specifications of programs that incorporate effects,
we can use predicate transformers.
\begin{code}
  wpFree : {C : Set} {R : C -> Set} -> ((c : C) -> (R c -> Set) -> Set) ->
    {a : Set} -> Free (eff C R) a -> (a -> Set) -> Set
  wpFree alg (Pure x) P = P x
  wpFree alg (Step c k) P = alg c \x -> wpFree alg (k x) P

  wpNondetAll : {a : Set} -> Free ENondet a ->
    (a -> Set) -> Set
  wpNondetAll S P = wpFree ptNondet S P
    where
    ptNondet : (c : CNondet) -> (RNondet c -> Set) -> Set
    ptNondet (Fail a) P = ¬ a
    ptNondet Split P = P True ∧ P False
\end{code}

We use pre- and postconditions to give a specification for a program.
If the precondition holds on the input,
the program needs to ensure the postcondition holds on the output.
\begin{code}
  record Spec (a : Set) : Set where
    constructor [[_,_]]
    field
      pre : Set
      post : a -> Set

  wpSpec : {a : Set} -> Spec a -> (a -> Set) -> Set
  wpSpec [[ pre , post ]] P = pre ∧ (∀ o -> post o -> P o)
\end{code}

The refinement relation expresses when one program is ``better'' than another.
We need to take into account the semantics we want to impose on the program,
so we define it in terms of the predicate transformer associated with the program.
\begin{code}
  _⊑_ : {a : Set} (pt1 pt2 : (a -> Set) -> Set) -> Set
  pt1 ⊑ pt2 = ∀ P -> pt1 P -> pt2 P
\end{code}

\section{Almost parsing regular languages}
As an example of using nondeterminism,
we can define the type of regular expressions |Regex| in Agda,
and a relation |Match| on |Regex| and |String|.
\begin{code}
  open import Data.Char
  open import Data.Char.Unsafe using (_≟_)
  String = List Char
\end{code}

\begin{code}
  data Regex : Set where
    Empty : Regex
    Epsilon : Regex
    Singleton : Char -> Regex
    _·_ : Regex -> Regex -> Regex
    _∣_ : Regex -> Regex -> Regex
    _* : Regex -> Regex

  data Match : Regex × String -> Set where
    Epsilon : Match (Epsilon , Nil)
    Singleton : {x : Char} -> Match (Singleton x , (x :: Nil))
    Concat : {l r : Regex} {ys zs : String} -> Match (l , ys) -> Match (r , zs) -> Match ((l · r) , (ys ++ zs))
    OrLeft : {l r : Regex} {xs : String} -> Match (l , xs) -> Match ((l ∣ r) , xs)
    OrRight : {l r : Regex} {xs : String} -> Match (r , xs) -> Match ((l ∣ r) , xs)
    StarNil : {r : Regex} -> Match ((r *) , Nil)
    StarConcat : {r : Regex} {xs : String} -> Match ((r · (r *)) , xs) -> Match ((r *) , xs)
\end{code}

Using nondeterminism as an effect, we create a function that takes a |Regex| and |String| and gives all potential matchings.
First, we introduce a utility function that nondeterministically splits a string into two parts.
\begin{code}
  record SplitList {a : Set} (xs : List a) : Set where
    constructor splitList
    field
      lhs : List a
      rhs : List a
      cat : xs == (lhs ++ rhs)

  allSplits : ∀ {a} -> (xs : List a) -> Free ENondet (SplitList xs)
  allSplits Nil = Pure (splitList Nil Nil refl)
  allSplits (x :: xs) = split
    (Pure (splitList Nil (x :: xs) refl))
    (allSplits xs >>= λ spl -> Pure (splitList (x :: SplitList.lhs spl) (SplitList.rhs spl) (cong (Cons x) (SplitList.cat spl))))
\end{code}

Given such a splitting and a matching regex for either side, we can find a match for the concatenation of the two regexes.
\begin{code}
  unsplit : ∀ {xs l r} (spl : SplitList xs) →
    Match (l , SplitList.lhs spl) →
    Match (r , SplitList.rhs spl) →
    Match ((l · r) , xs)
  unsplit (splitList lhs rhs refl) ml mr = Concat ml mr
\end{code}

\begin{code}
  match : (r : Regex) (xs : String) -> Free ENondet (Match (r , xs))
  match Empty xs = fail
  match Epsilon Nil = Pure Epsilon
  match Epsilon (x :: xs) = fail
  match (Singleton c) Nil = fail
  match (Singleton c) (x :: Nil) with c ≟ x
  match (Singleton c) (.c :: Nil) | yes refl = Pure Singleton
  match (Singleton c) (x :: Nil) | no ¬p = fail
  match (Singleton c) (_ :: _ :: _) = fail
  match (l · r) xs = allSplits xs >>=
    λ spl -> match l (SplitList.lhs spl) >>=
    λ ml -> match r (SplitList.rhs spl) >>=
    λ mr -> Pure (unsplit spl ml mr)
  match (l ∣ r) xs = split
    (match l xs >>= λ ml -> Pure (OrLeft ml))
    (match r xs >>= λ mr -> Pure (OrRight mr))
\end{code}
  Unfortunately, we get stuck in the case of |_*|, since it is not immediately obvious that this terminates.
  We just fail in this case.
\begin{code}
  match (r *) xs = fail
\end{code}

Still, we can prove that this program works, as long as the regex does not contain |_*|.
Since the type guarantees that all output is a correct match,
we only need to ensure that there is output.
Thus, the precondition states that the regex contains no Kleene star,
and the postcondition does not give any restrictions on the output.
\begin{code}
  hasNo* : Regex -> Set
  hasNo* Empty = ⊤
  hasNo* Epsilon = ⊤
  hasNo* (Singleton x) = ⊤
  hasNo* (l · r) = hasNo* l ∧ hasNo* r
  hasNo* (l ∣ r) = hasNo* l ∧ hasNo* r
  hasNo* (r *) = ⊥

  pre : (r : Regex) (xs : String) -> Set
  pre r xs = hasNo* r
  post : (r : Regex) (xs : String) -> Match (r , xs) -> Set
  post _ _ _ = ⊤
\end{code}
If we now want to give a correctness proof with respect to these pre- and postconditions,
we run into an issue in cases where the definition makes use of the |_>>=_| operator.
The |wpFree|-based semantics completely unfolds the left hand side,
before it can talk about the right hand side.
We solve this by using the following lemma to replace the left hand side with its specification.
\begin{code}
  wpBind : ∀ {a b} post (mx : Free ENondet a) (f : a -> Free ENondet b) ->
    wpNondetAll mx post ->
    ∀ P -> (∀ x -> post x -> wpNondetAll (f x) P) ->
    wpNondetAll (mx >>= f) P
  wpBind post (Pure x) f mxH P postH = postH x mxH
  wpBind post (Step (Fail x) k) f mxH P postH = mxH
  wpBind post (Step Split k) f (mxHt , mxHf) P postH = wpBind post (k True) f mxHt P postH , wpBind post (k False) f mxHf P postH
\end{code}

The correctness proof essentially does the same induction on the |Regex| as the definition of |match| does.
Since we make use of |allSplits| in the definition, we first give its correctness proof.
\begin{code}
  allSplitsCorrect : ∀ (xs : String) →
    wpNondetAll (allSplits xs) (λ _ → ⊤)
  allSplitsCorrect Nil = tt
  allSplitsCorrect (x :: xs) = tt , wpBind (const ⊤) (allSplits xs) _ (allSplitsCorrect xs) _ λ _ _ → tt
\end{code}
Then, using |wpBind|, we incorporate this proof in the correctness proof of |match|.
\begin{code}
  pf : ∀ r xs → wpSpec [[ pre r xs , post r xs ]] ⊑ wpNondetAll (match r xs)
  pf Empty xs P (preH , postH) = λ ()
  pf Epsilon Nil P (preH , postH) = postH Epsilon tt
  pf Epsilon (x :: xs) P (preH , postH) = λ ()
  pf (Singleton c) Nil P (preH , postH) = λ ()
  pf (Singleton c) (x :: Nil) P (preH , postH) with c ≟ x
  pf (Singleton c) (.c :: Nil) P (preH , postH) | yes refl = postH Singleton tt
  ... | no ¬p = λ {Singleton → ¬p refl}
  pf (Singleton c) (_ :: _ :: _) P (preH , postH) = λ ()
  pf (l · r) xs P ((preHl , preHr) , postH) =
    wpBind (const ⊤) (allSplits xs) _ (allSplitsCorrect xs) P λ spl _ →
    wpBind (const ⊤) (match l _) _ (pf _ _ _ (preHl , λ _ _ -> tt)) _ λ ml _ →
    wpBind (const ⊤) (match r _) _ (pf _ _ _ (preHr , λ _ _ -> tt)) _ λ mr _ →
    postH _ tt
  pf (l ∣ r) xs P ((preHl , preHr) , postH) =
    wpBind (const ⊤) (match l xs) _ (pf _ _ _ (preHl , λ _ _ -> tt)) _ (λ ml _ → postH _ tt) ,
    wpBind (const ⊤) (match r xs) _ (pf _ _ _ (preHr , λ _ _ -> tt)) _ (λ mr _ → postH _ tt)
  pf (r *) xs P (() , postH)
\end{code}

\section{Combining nondeterminism and general recursion}
In order to give a regex parser that also supports the Kleene star,
we add another effect: general recursion.

Here is the corresponding predicate transformer:
\begin{code}
wpRec : {!!}
wpRec = {!!}
\end{code}

The original |Free| monad is modified to support a list of effects instead of a single one,
which corresponds to taking the coproduct of the functors that |Free| is a free monad over.
\begin{code}
module Combinations where
  data Free (es : List Effect) (a : Set) : Set where
    Pure : a -> Free es a
    Step : {e : Effect} (i : e ∈ es) (c : Effect.C e) (k : Effect.R e c -> Free es a) -> Free es a
\end{code}

Now we need give new definitions of |wp|, |wpNondet| and |wpRec|.
\begin{code}
  wp : {a b : Set} -> (a -> Free Nil b) -> (a -> b -> Set) -> (a -> Set)
  wp = {!!}
  wpNondet : forall {a b es} -> (i : ENondet ∈ es) -> (a -> Free es b) -> (a -> Free (delete es i) b -> Set) -> (a -> Set)
  wpNondet = {!!}
\end{code} -- or make the smart constructors take |ENondet ∈ es| and the predicate transformers take |Free (ENondet :: es) b| to |Free es b|?

\section{Recursively parsing every regular expression}

Now we are able to handle the Kleene star:

We can also show correctness in the case of |*|.

However, in this proof we do not show termination of the parsing, so it is just a proof of partial correctness.
To prove termination, it is easier to write a new parser that refines the previous implementation.

\section{Termination, using derivatives}
We can use the Brzozowski derivative to advance the regular expression a single character, giving the function |dmatch|.

Since |dmatch| always consumes a character before going in recursion, we can easily prove it calls itself on smaller arguments.
This means that for all input values, after substituting itself in the definition enough times, we get rid of all (general) recursion.
In other words: |dmatch| terminates.

Moreover, |dmatch| is a refinement of |match|, which means it is also correct:

\section{Different viewpoints of grammars}
In classical logic, a language is no more than a set of strings, or a predicate over strings: |String -> Set|.
Constructively, such predicates (even when decidable) are not very useful: the language $\{xs \mid xs \text{is a valid proof of the Riemann Hypothesis} \}$ has no defined cardinality.
To make them more amenable to reasoning, we impose structure on languages, for example by giving their definition as a regular expression.
For more complicated grammars than regular expressions, we will use the abstract representation of grammars by Kasper Brink.

Alternatively, we can use the Brzozowski derivative to ensure we can step though the symbols of the language,
so we get the coinductive trie of Andeas Abel:

Our last viewpoint of grammar is a much more computational one: the list-of-succesful-parses type.

To unify these different viewpoints, we will apply algebraic effects.

\section{Parsing as effect}
While we can follow the traditional development of parsers from nondeterministic state,
algebraic effects allow us to introduce new effects,
which saves us bookkeeping issues.
The |EParser| effect has a single command, which consumes the next token from the input string, or fails if the string is empty.

An algebraic parser combines the effects of |ENondet| and |EParser|, which we will write in one predicate transformer:

This allows us to define the language of an algebraic parser: all strings such that the postcondition ``the unmatched string is empty'' is satisfied.

It is also possible to give handlers that convert algebraic parsers to a trie, or to a list-of-successes function:

\section{From abstract grammars to algebraic parsers}
The parser for the dependent grammar is similar in approach to |match|,
but we modify the type to be recursive from (A : Nonterminal) to [[ A ]].
Compare the |generateParser| function by Kasper Brink.

Partial correctness is relatively simple to show as soon as we define the semantics of grammars.

Termination is somewhat more subtle: since we call the same nonterminal repeatedly,
we cannot get rid of all recursion after enough substitutions of the definition.
Consider the language given by $E -> 'a' E \mid 'b'$.
However, we can show that substituting a fixed number of times, and then giving up using |fail|.
If each right hand side has a nonterminal, then the parser terminates in this weaker sense.

\section{Left factorisation?}
In that proof, do we need to left factorise the language? In that case, can we say something about that operation?
\end{document}

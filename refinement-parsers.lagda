\documentclass{llncs}

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

\title{Verified parsers using the refinement calculus and algebraic effects}
\author{Tim Baanen \and Wouter Swierstra}
\institute{Utrecht University
\email{\{t.baanen@vu.nl,w.s.swierstra@uu.nl\}}}
%
\maketitle              % typeset the header of the contribution

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
  Fail : CNondet
  Choice : CNondet
RNondet : CNondet -> Set
RNondet Fail = ⊥
RNondet Choice = Bool

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
%if style == newcode
\begin{code}
  _<$>_ : ∀ {a b e} -> (a → b) → Free e a → Free e b
  f <$> mx = mx >>= λ x → Pure (f x)
\end{code}
%endif
The easiest way to use effects is with smart constructors:
\begin{code}
  fail : ∀ {a} -> Free ENondet a
  fail {a} = Step Fail magic
  choice : ∀ {a} -> Free ENondet a -> Free ENondet a -> Free ENondet a
  choice S₁ S₂ = Step Choice λ b -> if b then S₁ else S₂
\end{code}

To give specifications of programs that incorporate effects,
we can use predicate transformers.
\begin{code}
  wpFree : {C : Set} {R : C -> Set} -> ((c : C) -> (R c -> Set) -> Set) ->
    {a : Set} -> Free (eff C R) a -> (a -> Set) -> Set
  wpFree alg (Pure x) P = P x
  wpFree alg (Step c k) P = alg c \x -> wpFree alg (k x) P
\end{code}
Interestingly, these predicate transformers are exactly the catamorphisms from |Free| to |Set|.

%if style == newcode
\begin{code}
module Nondet where
\end{code}
%endif
\begin{code}
  ptAll : (c : CNondet) -> (RNondet c -> Set) -> Set
  ptAll Fail P = ⊤
  ptAll Choice P = P True ∧ P False
\end{code}

%if style == newcode
\begin{code}
module NoCombination2 where
  open NoCombination
  open Nondet
\end{code}
%endif
\begin{code}
  wpNondetAll : {a : Set} -> Free ENondet a ->
    (a -> Set) -> Set
  wpNondetAll S P = wpFree ptAll S P
\end{code}

We use pre- and postconditions to give a specification for a program.
If the precondition holds on the input,
the program needs to ensure the postcondition holds on the output.
\begin{code}
module Spec where
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
%if style == newcode
\begin{code}
  ⊑-refl : ∀ {a} {pt : (a -> Set) -> Set} -> pt ⊑ pt
  ⊑-refl P x = x
\end{code}
%endif

\section{Almost parsing regular languages}
%if style == newcode
\begin{code}
open import Data.Char using (Char; _≟_)
String = List Char
\end{code}
%endif
To see how we can use the |Free| monad for writing and verifying a parser,
and more specifically how we use the |ENondet| effect for writing
and the |wpNondetAll| semantics for verifying a parser,
we will look at parsing a given regular language.
Our approach is first to define the specification of a parser,
then inspect this specification to write the first implementation and prove (partial) correctness of this implementation.
We will later improve this implementation by refining it.
\begin{Def}[\cite{dragon-book}]
The class of \emph{regular languages} is the smallest class such that:
\begin{itemize}
\item the empty language is regular,
\item the language containing only the empty string is regular,
\item for each character \texttt{x}, the language containing only the string |"x"| is regular,
\item the union and concatenation of regular languages are regular, and
\item the repetition of a regular language is regular.
\end{itemize}
\end{Def}

A regular language can defined using a regular expression,
which we will represent as an element of the |Regex| datatype.
An element of this type represents the syntax of a regular language,
and we will generally identify a regular expression with the language it denotes.
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
Here, |Empty| is an expression for empty language (which matches no strings at all),
while |Epsilon| is an expression for the language of the empty string (which matches exactly one string: |""|).

What should a parser for regular expressions output?
Perhaps it could return a |Bool| indicating whether a given string matches the regular expression,
or we could annotate the regular expression with capture groups,
and say that the output of the parser maps each capture group to the substring that the capture group matches.
In this case, we define the return type to be a parse tree mirroring the structure of the expression.
\begin{code}
tree : Regex -> Set
tree Empty          = ⊥
tree Epsilon        = ⊤
tree (Singleton _)  = Char
tree (l ∣ r)        = Either (tree l) (tree r)
tree (l · r)        = Pair (tree l) (tree r)
tree (r *)          = List (tree r)
\end{code}

In Agda, we can represent the semantics of the |Regex| type
by giving a relation between a |Regex| and a |String| on the one hand (the input of the matcher),
and a parse tree on the other hand (the output of the parser).
Note that the |tree| type itself is not sufficient to represent the semantics,
since it does not say which strings result in any given parse tree.
If the |Regex| and |String| do not match, there should be no output,
otherwise the output consists of all relevant parse trees.
We give the relation using the following inductive definition:
\begin{code}
data Match : (r : Regex) -> String -> tree r -> Set where
  Epsilon     : Match Epsilon Nil tt
  Singleton   : (implicit(x : Char)) Match (Singleton x) (x :: Nil) x
  OrLeft      : (implicit(l r : Regex)) (implicit(xs : String)) (implicit(x : tree l)) Match l xs x -> Match (l ∣ r) xs (Inl x)
  OrRight     : (implicit(l r : Regex)) (implicit(xs : String)) (implicit(x : tree r)) Match r xs x -> Match (l ∣ r) xs (Inr x)
  Concat      : (implicit(l r : Regex)) (implicit(ys zs : String)) (implicit(y : tree l)) (implicit(z : tree r)) Match l ys y -> Match r zs z -> Match (l · r) (ys ++ zs) (y , z)
  StarNil     : (implicit(r : Regex)) Match (r *) Nil Nil
  StarConcat  : (implicit(r : Regex)) (implicit(xs : String)) (implicit(y : tree r)) (implicit(ys : List (tree r))) Match (r · (r *)) xs (y , ys) -> Match (r *) xs (y :: ys)
\end{code}
Note that there is no constructor for |Match Empty xs ms| for any |xs| or |ms|,
which we interpret as that there is no way to match the |Empty| language with a string |xs|.
Similarly, the only constructor for |Match Epsilon xs ms| is where |xs| is the empty string |Nil|.

Since the definition of |Match| allows for multiple ways that a given |Regex| and |String| may match,
such as in the trivial case where the |Regex| is of the form |r ∣ r|,
and it also has cases where there is no way to match a |Regex| and a |String|,
such as where the |Regex| is |Empty|,
we can immediately predict some parts of the implementation.
Whenever we encounter an expression of the form |l ∣ r|, we make a nondeterministic |Choice| between either |l| or |r|.
Similarly, whenever we encounter the |Empty| expression, we immediately |fail|.
In the previous analysis steps, we have already assumed that we implement the parser by structural recursion on the |Regex|,
so let us consider other cases.

The implementation for concatenation is not as immediately obvious.
One way that we can deal with it is to change the type of the parser.
Instead write a parser that returns the unmatched portion of the string,
and when we have to match a regular expression of the form |l · r| with a string |xs|,
we match |l| with |xs| giving a left over string |ys|, then match |r| with |ys|.
We can also do without changing the return values of the parser,
by nondeterministically splitting the string |xs| into |ys ++ zs|.
That is what we do in a helper function |allSplits|,
which nondeterministically chooses such |ys| and |zs| and returns them as a pair.
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
  allSplits : (Forall(a)) (xs : List a) -> Free ENondet (List a × List a)
  allSplits Nil = Pure (Nil , Nil)
  allSplits (x :: xs) = choice
    (Pure (Nil , (x :: xs)))
    (allSplits xs >>= λ {(ys , zs) → Pure ((x :: ys) , zs)})
\end{code}

Armed with this helper function, we can write the first part of a nondeterministic regular expression matcher,
that does a case distinction on the expression and then checks that the string has the correct format.
\begin{code}
  match : (r : Regex) (xs : String) -> Free ENondet (tree r)
  match Empty xs = fail
  match Epsilon Nil = Pure tt
  match Epsilon xs@(_ :: _) = fail
  match (Singleton c) Nil = fail
  match (Singleton c) (x :: Nil) with c ≟ x
  match (Singleton c) (.c :: Nil) | yes refl = Pure c
  match (Singleton c) (x :: Nil) | no ¬p = fail
  match (Singleton c) xs@(_ :: _ :: _) = fail
  match (l · r) xs = do
    (ys , zs) <- allSplits xs
    y <- match l ys
    z <- match r zs
    Pure (y , z)
  match (l ∣ r) xs = choice (Inl <$> match l xs) (Inr <$> match r xs)
\end{code}
Unfortunately, we get stuck in the case of |_*|.
We could do a similar construction to |l · r|,
where we split the string into two parts and match the first part with |r| and the second part with |r *|,
but this runs afoul of Agda's termination checker.
Since there is no easy way to handle this case for now,
we just |fail| when we encounter a regex |r *|.
\begin{code}
  match (r *) xs = fail
\end{code}

Still, we can prove that this matcher works, as long as the regex does not contain |_*|.
In other words, we can prove that the |match| function refines a specification
where the precondition states that the regex contains no Kleene star,
and the postcondition states that the matching is correct,
with respect to the type |Match|.
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
  post : (r : Regex) (xs : String) -> tree r -> Set
  post = Match
\end{code}

If we now want to give a correctness proof with respect to these pre- and postconditions,
we run into an issue in cases where the definition makes use of the |_>>=_| operator.
The |wpFree|-based semantics completely unfolds the left hand side,
before it can talk about the right hand side.
Whenever our matcher makes use of recursion on the left hand side of a |_>>=_| (as we do in |allSplits| and in the cases of |l · r| and |l ∣ r|),
we cannot make progress in our proof without reducing this left hand side to a recursion-less expression.
We solve this by using the following lemma to replace the left hand side with a postcondition.
\begin{code}
  wpBind : ∀ {a b} post (mx : Free ENondet a) (f : a -> Free ENondet b) ->
    wpNondetAll mx post ->
    ∀ P -> (∀ x -> post x -> wpNondetAll (f x) P) ->
    wpNondetAll (mx >>= f) P
  wpBind post (Pure x) f mxH P postH = postH x mxH
  wpBind post (Step Fail k) f mxH P postH = mxH
  wpBind post (Step Choice k) f (mxHt , mxHf) P postH = wpBind post (k True) f mxHt P postH , wpBind post (k False) f mxHf P postH
\end{code}
This lemma is a specialization of the left compositionality property,
which states that we can refine on the left hand side of a bind.\todo{cite?}

The correctness proof closely matches the structure of |match| (and by extension |allSplits|).
It uses the same recursion on |Regex| as in the definition of |match|.
Since we make use of |allSplits| in the definition, we first give its correctness proof.
\begin{code}
  allSplitsSound : ∀ (xs : String) ->
    wpSpec [[ ⊤ , (λ {(ys , zs) → xs == ys ++ zs})]] ⊑ wpNondetAll (allSplits xs)
  allSplitsSound Nil        P (fst , snd) = snd _ refl
  allSplitsSound (x :: xs)  P (fst , snd) = snd _ refl ,
    wpBind _ (allSplits xs) _ (allSplitsSound xs _ (tt , λ _ → id)) P ?
\end{code}
Then, using |wpBind|, we incorporate this correctness proof in the correctness proof of |match|.
Apart from having to introduce |wpBind|, the proof essentially follows automatically from the definitions.
\begin{code}
  matchSound : ∀ r xs -> wpSpec [[ pre r xs , post r xs ]] ⊑ wpNondetAll (match r xs)
  matchSound Empty xs P (preH , postH) = tt
  matchSound Epsilon Nil P (preH , postH) = postH _ Epsilon
  matchSound Epsilon (x :: xs) P (preH , postH) = tt
  matchSound (Singleton x) Nil P (preH , postH) = tt
  matchSound (Singleton x) (c :: Nil) P (preH , postH) with x ≟ c
  matchSound (Singleton x) (c :: Nil) P (preH , postH) | yes refl = postH _ Singleton
  matchSound (Singleton x) (c :: Nil) P (preH , postH) | no ¬p = tt
  matchSound (Singleton x) (_ :: _ :: _) P (preH , postH) = tt
  matchSound (l · r) xs P (preH , postH) = ? {- wpBind (allSplits xs) _ P _
    (allSplitsSound xs _ (_ , (λ {(ys , zs) splitH y lH z rH → postH (y , z)
    (coerce (cong (λ xs → Match _ xs _) (sym splitH)) (Concat lH rH))}))) -}
  matchSound (l ∣ r) xs P ((preL , preR) , postH) = ? {-
    matchSound l xs _ (preL , λ o x -> postH o (OrLeft x)) ,
    matchSound r xs _ (preR , λ o x -> postH o (OrRight x)) -}
  matchSound (r *) xs P (() , postH)
\end{code}

\section{Combining nondeterminism and general recursion}
The matcher we have defined in the previous section is unfinished,
since it is not able to handle regular expressions that incorporate the Kleene star.
The fundamental issue is that the Kleene star allows for arbitrarily many distinct matchings in certain cases.
For example, matching |Epsilon *| with the string |Nil| will allow for repeating the |Epsilon| arbitrarily often, since |Epsilon · (Epsilon *)| is equivalent to both |Epsilon| and |Epsilon *|.
Thus, we cannot fix |match| by improving Agda's termination checker.

What we will do instead is to deal with the recursion as an effect.
A recursively defined (dependent) function of type |(i : I) -> O i|
can instead be given as an element of the type |(i : I) -> Free (ERec I O) (O i)|,
where |ERec I O| is the effect of \emph{general recursion}~\cite{McBride-totally-free}:
\begin{code}
ERec : (I : Set) (O : I -> Set) -> Effect
ERec I O = eff I O
\end{code}

We are not yet done now that we have defined the missing effect,
since replacing the effect |ENondet| with |ERec (Pair Regex String) (List String)| does not allow for nondeterminism anymore,
so while the Kleene star might work, the other parts of |match| do not work anymore.
We need a way to combine the two effects.

We can combine two effects in a straightforward way: given |eff C₁ R₁| and |eff C₂ R₂|,
we can define a new effect by taking the disjoint union of the commands and responses,
resulting in |eff (Either C₁ C₂) [ R₁ , R₂ ]|,
where |[ R₁ , R₂ ]| is the unique map given by applying |R₁| to values in |C₁| and |R₂| to |C₂|.
If we want to support more effects, we can repeat this process of disjoint unions,
but this quickly becomes somewhat cumbersome.
For example, the disjount union construction is associative,
but we would need to supply a proof of this whenever the associations of our types do not match.

Instead of building a new effect type, we modify the |Free| monad to take a list of effects instead of a single effect.
The |Pure| constructor remains as it is,
while the |Step| constructor takes an index into the list of effects and the command and continuation for the effect with this index.
%if style == newcode
\begin{code}
module Combinations where
\end{code}
%endif
\begin{code}
  data Free (es : List Effect) (a : Set) : Set where
    Pure : a -> Free es a
    Step : {e : Effect} (i : e ∈ es) (c : Effect.C e) (k : Effect.R e c -> Free es a) -> Free es a
\end{code}
By using a list of effects instead of allowing arbitrary disjoint unions,
we have effectively chosen a canonical association order of these unions.
Since the disjoint union is also commutative, it would be cleaner to have the collection of effects be unordered as well,
but there does not seem to be a data type built into Agda that allows for unordered collections.

To make use of the new definition of |Free|, we need to translate the previous constructions.
We can define the monadic bind |_>>=_| in the same way as in the previous definition of |Free|.
%if style == newcode
\begin{code}
  _>>=_ : ∀ {a b es} -> Free es a -> (a -> Free es b) -> Free es b
  Pure x >>= f = f x
  Step i c k >>= f = Step i c λ x -> k x >>= f
  _>>_ : ∀ {a b es} → Free es a → Free es b → Free es b
  mx >> my = mx >>= const my
  >>=-assoc : ∀ {a b c es} (S : Free es a) (f : a -> Free es b) (g : b -> Free es c) ->
    (S >>= f) >>= g == S >>= (λ x -> f x >>= g)
  >>=-assoc (Pure x) f g = refl
  >>=-assoc (Step i c k) f g = cong (Step i c) (extensionality λ x -> >>=-assoc (k x) _ _)
  >>=-Pure : ∀ {a es} (S : Free es a) ->
    S >>= Pure == S
  >>=-Pure (Pure x) = refl
  >>=-Pure (Step i c k) = cong (Step i c) (extensionality λ x -> >>=-Pure (k x))
  _<$>_ : ∀ {a b es} -> (a → b) → Free es a → Free es b
  f <$> mx = mx >>= λ x → Pure (f x)
\end{code}
%endif
We also to make a small modification to the smart constructors for nondeterminism,
since they now need to keep track of their position within a list of effects.
Most of the bookkeeping can be offloaded to Agda's instance argument solver,
as long as we indic
\todo{Use Agda's instance arguments for |iND| and |iRec| instead of explicit arguments? Might make it a bit more straightforward to write code with it, but apparently the solver is not always smart enough to use them...}
\begin{code}
  fail : ∀ {a es} ⦃ iND : ENondet ∈ es ⦄ -> Free es a
  fail ⦃ iND ⦄ = Step iND Fail magic
  choice : ∀ {a es} ⦃ iND : ENondet ∈ es ⦄ -> Free es a -> Free es a -> Free es a
  choice ⦃ iND ⦄ S₁ S₂ = Step iND Choice λ b -> if b then S₁ else S₂

  call : ∀ {I O es} -> ⦃ iRec : ERec I O ∈ es ⦄ -> (i : I) -> Free es (O i)
  call ⦃ iRec ⦄ i = Step iRec i Pure
\end{code}
For convenience of notation, we introduce the |(RecArr _ es _)| notation for general recursion,
i.e. Kleisli arrows into |Free (ERec _ _ :: es)|.
\begin{code}
  RecArr' : (C : Set) (es : List Effect) (R : C → Set) → Set
  (RecArr C es R) = (c : C) -> Free (eff C R :: es) (R c)
\end{code}

\begin{code}
instance
  inHead : ∀ {a} {x : a} {xs : List a} → x ∈ (x :: xs)
  inHead = ∈Head
  inTail : ∀ {a} {x x' : a} {xs : List a} → ⦃ i : x ∈ xs ⦄ → x ∈ (x' :: xs)
  inTail ⦃ i ⦄ = ∈Tail i
\end{code}

Since we want the effects to behave compositionally,
the semantics of the combination of effects should be similarly found in a list of predicate transformers.
The type |List ((c : C) -> (R c -> Set) -> Set)| is not sufficient,
since we need to ensure the types match up.
Using a dependent type we can define a list of predicate transformers for a list of effects:
%if style == newcode
\begin{code}
module Stateless where
  open Combinations
  open Spec
\end{code}
%endif
\todo{We introduce a type |PT| hwich includes a monotonicity requirement.}
\begin{code}
  record PT (e : Effect) : Set where
    constructor mkPT
    field
      pt : (c : Effect.C e) → (Effect.R e c → Set) → Set
      mono : ∀ c → (P P' : Effect.R e c → Set) → P ⊆ P' → pt c P → pt c P'

  data PTs : List Effect -> Set where
    Nil : PTs Nil
    _::_ : ∀ {e es} -> PT e -> PTs es -> PTs (e :: es)
\end{code}

Given a such a list of predicate transformers,
defining the semantics of an effectful program is a straightforward generalization of |wpFree|.
The |Pure| case is identical, and in the |Step| case we find the predicate transformer at the corresponding index to the effect index |i : e ∈ es| using the |lookupPT| helper function.
\begin{code}
  lookupPT : ∀ {C R es} (pts : PTs es) (i : eff C R ∈ es) -> (c : C) -> (R c -> Set) -> Set
  lookupPT (pt :: pts) ∈Head = PT.pt pt
  lookupPT (pt :: pts) (∈Tail i) = lookupPT pts i
\end{code}
%if style == newcode
\begin{code}
  lookupMono : ∀ {C R es} (pts : PTs es) (i : eff C R ∈ es) -> ∀ c P P' → P ⊆ P' → lookupPT pts i c P → lookupPT pts i c P'
  lookupMono (pt :: pts) ∈Head = PT.mono pt
  lookupMono (pt :: pts) (∈Tail i) = lookupMono pts i
\end{code}
%endif
This results in the following definition of |wpFree| for combinations of effects.
\begin{code}
  wpFree : forall {a es} (pts : PTs es) ->
    Free es a -> (a -> Set) -> Set
  wpFree pts (Pure x) P = P x
  wpFree pts (Step i c k) P = lookupPT pts i c (λ x -> wpFree pts (k x) P)
\end{code}

In the new definition of |match|, we want to combine the effects of nondeterminism and general recursion.
To verify this definition, we need to give its semantics,
for which we need to give the list of predicate transformers to |wpFree|.
For nondeterminism we alread have the predicate transformer |ptAll|.
However, it is not as easy to give a predicate transformer for general recursion,
since the intended semantics of a recursive call depend
on the function that is being called, i.e. the function that is being defined.

However, if we have a specification of a function of type |(i : I) -> O i|,
for example in terms of a relation of type |(i : I) -> O i -> Set|,
we can define a predicate transformer:
\begin{code}
  ptRec : ∀ {I : Set} {O : I -> Set} -> ((i : I) -> O i -> Set) -> PT (ERec I O)
  PT.pt (ptRec R) i P = ∀ o -> R i o -> P o
  PT.mono (ptRec R) = ?
\end{code}
For example, the |Match| relation serves as a specification for the |match| function.
If we use |ptRec R| as a predicate transformer to check that a recursive function satisfies the relation |R|,
then we are proving \emph{partial correctness}, since we assume each recursive call terminates according to the relation |R|.

\section{Recursively parsing every regular expression}

Now we are able to handle the Kleene star:

\begin{code}
  allSplits : (Forall(a es)) ⦃ iND :  ENondet ∈ es ⦄ (xs : List a) -> Free es (List a × List a)
  allSplits Nil = Pure (Nil , Nil)
  allSplits (x :: xs) = choice
    (Pure (Nil , (x :: xs)))
    (allSplits xs >>= λ {(ys , zs) → Pure ((x :: ys) , zs)})

  match : (Forall(es)) ⦃ iND : ENondet ∈ es ⦄ → (RecArr (Regex × String) es (λ {(r , xs) -> tree r}))
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
    y <- call (l , ys)
    z <- call (r , zs)
    Pure (y , z)
  match ((l ∣ r) , xs) = choice
    (Inl <$> call (l , xs))
    (Inr <$> call (r , xs))
  match ((r *) , Nil) = Pure Nil
  match ((r *) , xs@(_ :: _)) = do
    (y , ys) <- call ((r · (r *)) , xs)
    Pure (y :: ys)
\end{code}

The effects we need to use for running |match| are a combination of nondeterminism and general recursion.
As discussed, we first need to give the specification for |match| before we can verify a program that makes use of |match|.
%if style == newcode
\begin{code}
  ptAll : PT ENondet
  PT.pt ptAll Fail P = ⊤
  PT.pt ptAll Choice P = P True ∧ P False
  PT.mono ptAll = ?
\end{code}
%endif
\begin{code}
  matchSpec : (r,xs : Pair Regex String) -> tree (Pair.fst r,xs) -> Set
  matchSpec (r , xs) ms = Match r xs ms

  wpMatch : (Forall(a)) Free (eff (Pair Regex String) (λ {(r , xs) -> tree r}) :: ENondet :: Nil) a ->
    (a -> Set) -> Set
  wpMatch = wpFree (ptRec matchSpec :: ptAll :: Nil)
\end{code}

In a few places, we use a recursive |call| instead of actual recursion.
One advantage to this choice is that in proving correctness,
we can use the specification of |match| directly,
without having to use the following rule of |consequence| in between.
Unfortunately, we still need |consequence| to deal with the call to |allSplits|.
\begin{code}
  consequence : ∀ {a b es pts P} (mx : Free es a) (f : a -> Free es b) ->
    wpFree pts mx (λ x -> wpFree pts (f x) P) == wpFree pts (mx >>= f) P
  consequence (Pure x) f = refl
  consequence (Step i c k) f = cong (lookupPT _ i c) (extensionality λ x -> consequence (k x) f)

  wpToBind : ∀ {a b es pts P} (mx : Free es a) (f : a -> Free es b) ->
    wpFree pts mx (λ x -> wpFree pts (f x) P) -> wpFree pts (mx >>= f) P
  wpToBind mx f H = subst id (consequence mx f) H

  wpFromBind : ∀ {a b es pts P} (mx : Free es a) (f : a -> Free es b) ->
    wpFree pts (mx >>= f) P -> wpFree pts mx (λ x -> wpFree pts (f x) P)
  wpFromBind mx f H = subst id (sym (consequence mx f)) H
\end{code}

We can reuse exactly the same proof to show |allSplits| is correct,
since we use the same semantics for the effects in |allSplits|.
%if style == newcode
\begin{code}
  allSplitsSound : ∀ (xs : String) ->
    wpSpec [[ ⊤ , (λ {(ys , zs) → xs == ys ++ zs})]] ⊑ wpMatch (allSplits (hiddenInstance(∈Tail ∈Head)) xs)
  allSplitsSound Nil        P (fst , snd) = snd _ refl
  allSplitsSound (x :: xs)  P (fst , snd) = snd _ refl ,
    ? -- wpToBind (allSplits (hiddenInstance(∈Tail ∈Head)) xs) (allSplitsSound xs _ (tt , (λ {(ys , zs) H → snd _ (cong (x ::_) H)})))
\end{code}
%endif
On the other hand, the correctness proof for |match| needs a bit of tweaking to deal with the difference in the recursive steps.
\begin{code}
  matchSound : ∀ r,xs -> wpSpec [[ ⊤ , matchSpec r,xs ]] ⊑ wpMatch (match (hiddenInstance(∈Head)) r,xs)
  matchSound (Empty , xs) P (preH , postH) = tt
  matchSound (Epsilon , Nil)       P (preH , postH) = postH _ Epsilon
  matchSound (Epsilon , (_ :: _))  P (preH , postH) = tt
  matchSound (Singleton c , Nil)            P (preH , postH) = tt
  matchSound (Singleton c , (x :: Nil))     P (preH , postH) with c ≟ x
  matchSound (Singleton c , (.c :: Nil))    P (preH , postH) | yes refl = postH _ Singleton
  matchSound (Singleton c , (x :: Nil))     P (preH , postH) | no ¬p = tt
  matchSound (Singleton c , (_ :: _ :: _))  P (preH , postH) = tt
  matchSound ((l · r) , xs) P (preH , postH) = ? {- coerce (sym (fold-bind (allSplits (hiddenInstance(∈Tail ∈Head)) xs) _ P _))
    (allSplitsSound xs _ (_ , (λ {(ys , zs) splitH y lH z rH → postH (y , z)
      (coerce (cong (λ xs → Match _ xs _) (sym splitH)) (Concat lH rH))}))) -}
  matchSound ((l ∣ r) , xs) P (preH , postH) =
    (λ o H -> postH _ (OrLeft H)) ,
    (λ o H -> postH _ (OrRight H))
\end{code}
Now we are able to prove correctness of |match| on a Kleene star.
\begin{code}
  matchSound ((r *) , Nil)        P (preH , postH) = postH _ StarNil
  matchSound ((r *) , (x :: xs))  P (preH , postH) = λ o H -> postH _ (StarConcat H)
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

\section{Termination, using derivatives}
Since recursion on the structure of a regular expression
does not guarantee termination of the parser,
we can instead perform recursion on the string to be parsed.
To do this, we make use of the Brzozowski derivative.
\begin{Def}[\cite{Brzozowski}]
The \introTerm{Brzozowski derivative} of a formal language |L| with respect to a character |x| consists of all strings |xs| such that |x :: xs ∈ L|.
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
  dmatch : (Forall(es)) ⦃ iND : ENondet ∈ es ⦄ -> (RecArr (Regex × String) es (λ {(r , xs) -> tree r}))
  dmatch (r , Nil) with matchEpsilon r
  ... | yes (ms , _)  = Pure ms
  ... | no ¬p         = fail
  dmatch (r , (x :: xs)) = integralTree r <$> call ((d r /d x) , xs)
\end{code}

Since |dmatch| always consumes a character before going in recursion, we can easily prove that each recursive call only leads to finitely many other calls.
This means that for each input value we can unfold the recursive step in the definition a bounded number of times and get a computation with no recursion.
Intuitively, this means that |dmatch| terminates on all input.
If we want to make this more formal, we need to consider what it means to have no recursion in the computation.
A definition for the |while| loop using general recursion looks as follows:
\begin{code}
  while : ∀ {es a} -> ⦃ iRec : ERec a (K a) ∈ es ⦄ -> (a -> Bool) -> (a -> a) -> (a -> Free es a)
  while cond body i = if cond i then Pure i else (call (body i))
\end{code}
We would like to say that some |while| loops terminate, yet the definition of |while| always contains a |call| in it.
Thus, the requirement should not be that there are no more calls left,
but that these calls are irrelevant.
A next intuitive idea could be the following:
if we make the recursive computation into a |Partial| computation by |fail|ing instead of |call|ing,
the |Partial| computation still works the same, i.e. it refines, the recursive computation.
However, this mixes the concepts of correctness and termination.
We want to see that the computation terminates with some output, without caring about which output this is.
Thus, we should only have a trivial postcondition |λ _ -> ⊤|.
We formalize this idea in the |terminates-in| predicate.
%if style == newcode
\begin{code}
  {-
  ∈-++ : ∀ {a x} {xs ys : List a} -> x ∈ ys -> x ∈ (xs ++ ys)
  ∈-++ {xs = Nil} i = i
  ∈-++ {xs = x :: xs} i = ∈Tail (∈-++ i)

  repeat : ∀ {a : Set} -> Nat -> (a -> a) -> a -> a
  repeat Zero f x = x
  repeat (Succ n) f x = repeat n f (f x) -- or |f (repeat n f x)| ?

  open import Data.Nat using (_+_; _≤_)
  -}
\end{code}
%endif
\begin{code}
  terminates-in : (Forall(C R es a)) (pts : PTs es) (f : (RecArr C es R)) (S : Free (eff C R :: es) a) → Nat → Set
  terminates-in pts f (Pure x) n = ⊤
  terminates-in pts f (Step ∈Head c k) Zero = ⊥
  terminates-in pts f (Step ∈Head c k) (Succ n) = terminates-in pts f (f c >>= k) n
  terminates-in pts f (Step (∈Tail i) c k) n = lookupPT pts i c (λ x → terminates-in pts f (k x) n)
\end{code}

Since |dmatch| always consumes a character before going in recursion,
we can bound the number of recursive calls with the length of the input string.
The proof goes by induction on this string.
Unfolding the recursive |call| gives |(dmatch (d r /d x , xs) >>= (Pure ∘ integralTree)|,
which we can rewrite in the lemma |terminates-fmap| using the associativity \meldTerm[monad laws]{monad law}.
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
    assoc (Step i c k) f g = cong (Step i c) (extensionality λ x → assoc (k x) f g)
    terminates-fmap : ∀ {C R es a b pts f} {g : a → b} n (S : Free (eff C R :: es) a) → terminates-in pts f S n → terminates-in pts f (S >>= (Pure ∘ g)) n
    terminates-fmap n (Pure x) H = H
    terminates-fmap {pts = pts} {f} {g} (Succ n) (Step ∈Head c k) H = subst (λ S → terminates-in pts f S n) (assoc (f c) k (Pure ∘ g)) (terminates-fmap n (f c >>= k) H)
    terminates-fmap {pts = pts} n (Step (∈Tail i) c k) H = lookupMono pts i c _ _ (λ x → terminates-fmap n (k x)) H
\end{code}
%endif

To show partial correctness of |dmatch|,
we can use the transitivity of the refinement relation.
If we apply transitivity, it suffices to show that |dmatch| is a refinement of |match|.
Our first step is to show that the derivative operator is correct,
i.e. |d r /d x| matches those strings |xs| such that |r| matches |x :: xs|.
\begin{code}
  derivativeCorrect : (Forall(x xs)) ∀ r -> (Forall(y)) Match (d r /d x) xs y -> Match r (x :: xs) (integralTree r y)
\end{code}
Since the definition of |d_/d_| uses the |integralTree| function,
we also prove the correctness of |integralTree|.
\begin{code}
  integralTreeCorrect  : ∀ r x xs y -> Match (d r /d x) xs y -> Match r (x :: xs) (integralTree r y)
\end{code}
All three proofs mirror the definitions of these functions,
being structured as a case distinction on the regular expression.
%if style == newcode
\begin{code}
  integralTreeCorrect (Singleton c) x xs y H with x ≟ c
  integralTreeCorrect (Singleton c) .c .Nil tt Epsilon | yes refl = Singleton
  integralTreeCorrect (Singleton c) x xs y () | no ¬p
  integralTreeCorrect (l ∣ r) x xs .(Inl _) (OrLeft H) = OrLeft (integralTreeCorrect l x xs _ H)
  integralTreeCorrect (l ∣ r) x xs .(Inr _) (OrRight H) = OrRight (integralTreeCorrect r x xs _ H)
  integralTreeCorrect (l · r) x xs y H with matchEpsilon l
  integralTreeCorrect (l · r) x .(ys ++ zs) (Inl (fst , snd)) (OrLeft (Concat {ys = ys} {zs} H H')) | yes p
    = Concat (integralTreeCorrect l x ys fst H) H'
  integralTreeCorrect (l · r) x xs (Inr y) (OrRight H) | yes (y' , H')
    = Concat H' (integralTreeCorrect r x xs y H)
  integralTreeCorrect (l · r) x .(ys ++ zs) (fst , snd) (Concat {ys = ys} {zs} H H') | no ¬p
    = Concat (integralTreeCorrect l x ys fst H) H'
  integralTreeCorrect (r *) x .(ys ++ zs) (fst , snd) (Concat {ys = ys} {zs} H H')
    = StarConcat (Concat (integralTreeCorrect r x ys fst H) H')

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

Before we can prove the correctness of |dmatch| in terms of |match|,
it turns out that we also need to describe |match| itself better.
To show |match| is refined by |dmatch|,
we need to prove that the output of |dmatch| is a subset of that of |match|.
Since |match| makes use of |allSplits|, we first prove
that |allSplits| returns all possible splittings of a string.
\begin{code}
  allSplitsComplete : (xs ys zs : String) (P : String × String → Set) →
    wpMatch (allSplits (hiddenInstance(∈Tail ∈Head)) xs) P → (xs == ys ++ zs) → P (ys , zs)
\end{code}
%if style == newcode
\begin{code}
  allSplitsComplete Nil Nil .Nil P H refl = H
  allSplitsComplete (x :: xs) Nil .(x :: xs) P H refl = Pair.fst H
  allSplitsComplete .(x :: ys ++ zs) (x :: ys) zs P H refl = allSplitsComplete (ys ++ zs) ys zs (λ {(ys' , zs') → P ((x :: ys') , zs')}) {! (coerce (fold-bind (allSplits ⦃ ∈Tail ∈Head ⦄ (ys ++ zs)) _ P _) (Pair.snd H)) !} refl
\end{code}
%endif
The proof mirrors |allSplits|, performing induction on |xs|.
Note that |allSplitsSound| and |allSplitsComplete| together show that |allSplits xs| is \meldTerm[equivalent!predicate transformers]{equivalent} to its specification |[[ ⊤ , λ {(ys , zs) -> xs == ys + zs}]]|,
in the sense of the |_≡_| relation.

Using the preceding lemmas, we can prove the partial correctness of |dmatch| by showing it refines |match|:
\begin{code}
  dmatchSound : ∀ r xs -> wpMatch (match (hiddenInstance(∈Head)) (r , xs)) ⊑ wpMatch (dmatch (hiddenInstance(∈Head)) (r , xs))
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
  dmatchSound (l · r)        (x :: xs)       P (fst , snd) = ?
  {-
  dmatchSound (l · r)        (x :: xs)       P (fst , snd) with matchEpsilon l
  dmatchSound (l · r)        (x :: xs)       P (fst , snd) o (OrLeft (Concat (hidden(ys = ys)) (hidden(zs)) Hl Hr)) | yes p =
    allSplitsComplete (x :: xs) (x :: ys) zs _
      ? -- (fst , coerce (fold-bind (allSplits (hiddenInstance(∈Tail ∈Head)) (ys ++ zs) >>= _) _ P _) snd)
      refl _ (derivativeCorrect _ Hl) _ Hr
  dmatchSound (l · r)        (x :: xs)       P (fst , snd) o (OrRight H) | yes (y , Hl)
    = fst _ Hl _ (integralTreeCorrect r x xs _ H)
  dmatchSound (l · r)        (x :: xs)       P (fst , snd) o (Concat (hidden(ys = ys)) (hidden(zs)) Hl Hr) | no ¬p =
    allSplitsComplete (x :: xs) (x :: ys) zs _
      ? -- (fst , (coerce (fold-bind (allSplits (hiddenInstance(∈Tail ∈Head)) (ys ++ zs) >>= _) _ P _) snd))
      refl _ (derivativeCorrect _ Hl) _ Hr
  -}
  dmatchSound (l ∣ r)        Nil             P (fst , snd) with matchEpsilon l | matchEpsilon r
  dmatchSound (l ∣ r)        Nil             P (fst , snd) | yes (ml , pl) | yes (mr , pr) = fst ml pl
  dmatchSound (l ∣ r)        Nil             P (fst , snd) | yes (ml , pl) | no ¬pr = fst ml pl
  dmatchSound (l ∣ r)        Nil             P (fst , snd) | no ¬pl | yes (mr , pr) = snd mr pr
  dmatchSound (l ∣ r)        Nil             P (fst , snd) | no ¬pl | no ¬pr = tt
  dmatchSound (l ∣ r)        (x :: xs)       P (fst , snd) = ?
  {-
  dmatchSound (l ∣ r)        (x :: xs)       P (fst , snd) o (OrLeft H)   = fst _ (derivativeCorrect _ H)
  dmatchSound (l ∣ r)        (x :: xs)       P (fst , snd) o (OrRight H)  = snd _ (derivativeCorrect _ H)
  -}
  dmatchSound (r *)          Nil             P H = H
  dmatchSound (r *)          (x :: xs)       P H = ?
  {-
  dmatchSound (r *)          (x :: xs)       P H ms (Concat ml mr)
    = H _ (Concat (derivativeCorrect _ ml) mr)
  -}
\end{code}
%endif

With the proof of |dmatchSound| finished, we can conclude that |dmatch| always returns a correct parse tree, i.e. that |dmatch| is sound.
However, |dmatch| is \emph{not} complete with respect to the |Match| relation:
since |dmatch| never makes a nondeterministic choice, it will not return all possible parse trees as specified by |Match|,
only the first tree that it encounters.
Still, we can express the property that |dmatch| finds a parse tree if it exists.
In other words, we will show that if there is a valid parse tree, |dmatch| returns any parse tree (and this is a valid tree by |dmatchSound|).
To express that |dmatch| returns something, we use a trivially true postcondition,
and replace the |ptAll| semantics for nondeterminism with |ptAny|:
\begin{code}
  dmatchComplete : ∀ r xs y →
    Match r xs y → wpFree (ptRec matchSpec :: ptAll :: Nil) (dmatch (hiddenInstance(∈Head)) (r , xs)) (λ _ → ⊤)
\end{code}
The proof is short, since |dmatch| can only |fail| when it encounters an empty string and a regex that does not match the empty string, contradicting the assumption immediately:
\begin{code}
  dmatchComplete r Nil y H with matchEpsilon r
  ... | yes p = tt
  ... | no ¬p = ? -- ¬p (_ , H)
  dmatchComplete r (x :: xs) = ?
  -- dmatchComplete r (x :: xs) y H y' H' = tt
\end{code}
Here we have demonstrated the power of predicate transformer semantics for effects:
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
they correspond almost directly to the |EParser| effect of the following section.
Another main difference between our implementation and \citeauthor{harper-regex}'s
is in the way the non-termination of |match| is resolved.
\citeauthor{harper-regex} uses the derivative operator to rewrite the expression in a standard form
which ensures that the |match| function terminates.
We use the derivative operator to implement a different matcher |dmatch| which is easily proved to be terminating,
then show that |match|, which we have already proven partially correct, is refined by |dmatch|.
The final major difference is that \citeauthor{harper-regex} uses manual verification of the program and our work is formally computer-verified.
Although our development takes more work, the correctness proofs give more certainty than the informal arguments made by \citeauthor{harper-regex}.
In general, choosing between informal reasoning and formal verification will always be a trade-off between speed and accuracy.

\section{Effects as unifying theory of parsers} \label{sec:contextFree}
In the previous section, we have developed a formally verified parser for regular languages.
The class of regular languages is small, and does not include most programming languages.
If we want to write a parser for a larger class of languages, we fist need a practical representation.
In classical logic, the most general concept of a formal language is no more than a set of strings, or a predicate over strings,
represented by the type |String -> Set|.
Constructively, such predicates (even when decidable) are not very useful: the language $\{\mathit{xs} \mid \mathit{xs} \text{ is a valid proof of the Riemann Hypothesis} \}$ has no defined cardinality.
To make them more amenable to reasoning, we impose structure on languages, for example by giving their definition as a regular expression.
When we have a more structured grammar, we can write a parser for these grammars,
and prove its partial correctness and termination, just as we did for regular expressions and |dmatch|.

One structure we can impose on languages is that we can always perform local operations,
in the style of the Brzozowski derivative.
This means we can decide whether a language |l| matches the empty string (as |matchEpsilon| does for regular languages),
and for each character |x|, we can compute the derivative |d l /d x|,
which contains exactly those |xs| such that |x :: xs| is in |l|.
Packaging up these two operations into a record type gives the \introTerm{coinductive trie} representation
of a formal language, as described by \citet{coinductive-trie}.
We augment the definition by including a list of the parser's output values for the empty string,
instead of a Boolean stating whether the language contains the empty string.
An empty list corresponds to the original |False|, while a non-empty list corresponds to |True|.
%if style == newcode
\begin{code}
module ContextFree where
  open import Size public
\end{code}
%endif
\begin{code}
  record Trie (i : Size) (a : Set) : Set where
    coinductive
    field
      ε : List a
      d_/d_ : (implicit(j : Size< i)) Char -> Trie j a
\end{code}
%if style == newcode
\begin{code}
  open Trie public
\end{code}
%endif
The definition of the |Trie| type is complicated by making it coinductive and using sized types.
We need |Trie| to be coinductive since it appears in a negative position in the |d_/d_| operator,
or viewed in another way, since the |Trie| type needs to be nested arbitrarily deeply to describe arbitrarily long strings.
The sized types help Agda to check that certain definitions terminate.
Despite being needed to ensure the |Trie| type is useful, the two complications do not play an important role in the remainder of the development.

\begin{Ex}
Let us look at two simple examples of definitions using the |Trie| type.
The first definition, |emptyTrie|, represents the empty language.
It does not contain the empty string, so |ε emptyTrie| is the empty list.
It also does not contain any string of the form |x :: xs|, so the derivatives of the empty trie are all the empty trie again.
\begin{code}
  emptyTrie : (Forall(i a)) Trie i a
  ε emptyTrie = Nil
  d emptyTrie /d x = emptyTrie
\end{code}
This is also an example of why we need the coinductive structure of the |Trie| type,
since the definition |d emptyTrie /d x = emptyTrie| is not productive for an inductive type.

The second example of a construction in the |Trie| type is the union operator,
which is straightforward to write out.
\begin{code}
  _∪t_ : (Forall(i a)) Trie i a -> Trie i a -> Trie i a
  ε (t ∪t t') = ε t ++ ε t'
  d (t ∪t t') /d x = (d t /d x) ∪t (d t' /d x)
\end{code}
\end{Ex}

We can also take a very computational approach to languages,
representing them by a parser.
This parser takes a string and returns a list of successful matches,
similar to the |ε| operator of the coinductive |Trie|.
\begin{code}
  Parser : Set -> Set
  Parser a = String -> List a
\end{code}

\subsection{Context-free grammars with |Productions|}
Using a |Trie| or a |Parser| to define a language requires a lot of low-level work,
since we first need to implement operations such as the union of a language or concatenation.
The |Regex| representation of regular languages has such operations built-in,
allowing us to have intuition on the level of grammar rather than operations.
A class of languages that is more expressive than the regular languages,
while remaining tractable in parsing is that of the \introTerm[context-free language]{context-free language}.
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
    Nonterminal : Set
    ⟦_⟧ : Nonterminal -> Set
    _≟n_ : Decidable {A = Nonterminal} _==_
\end{code}
The elements of the type |Char| are the \introTerm{terminal} symbols, for example characters or tokens.
The elements of the type |Nonterminal| are the \introTerm{nonterminal} symbols, representing the language constructs.
As for |Char|, we also need to be able to decide the equality of nonterminals.
The (disjoint) union of |Char| and |Nonterminal| gives all the symbols that we can use in defining the grammar.
%if style == newcode
\begin{code}
module Grammar (gs : GrammarSymbols) where
  open ContextFree
  open GrammarSymbols gs
\end{code}
%endif
\begin{code}
  Symbol = Either Char Nonterminal
  Symbols = List Symbol
\end{code}
For each nonterminal |A|, our goal is to parse a string into a value of type |⟦ A ⟧|,
based on a set of production rules.
A production rule $A \to xs$ gives a way to expand the nonterminal |A| into a list of symbols |xs|,
such that successfully matching each symbol of |xs| with parts of a string
gives a match of the string with |A|.
Since matching a nonterminal symbol |B| with a (part of a) string results in a value of type |⟦ B ⟧|,
a production rule for |A| is associated with a \introTerm{semantic function} that takes all values arising from submatches
and returns a value of type |⟦ A ⟧|,
as expressed by the following type:
\begin{code}
  ⟦_∥_⟧ : Symbols -> Nonterminal -> Set
  ⟦ Nil           ∥ A ⟧ = ⟦ A ⟧
  ⟦ Inl x  :: xs  ∥ A ⟧ = ⟦ xs ∥ A ⟧
  ⟦ Inr B  :: xs  ∥ A ⟧ = ⟦ B ⟧ -> ⟦ xs ∥ A ⟧
\end{code}
Now we can define the type of production rules. A rule of the form $A \to B c D$ is represented as |prod A (Inr B :: Inl c :: Inr D :: Nil) f| for some |f|.
\begin{code}
  record Production : Set where
    constructor prod
    field
      lhs : Nonterminal
      rhs : Symbols
      sem : ⟦ rhs ∥ lhs ⟧
\end{code}
%if style == newcode
\begin{code}
  Productions = List Production
\end{code}
%endif
We use the abbreviation |Productions| to represent a list of productions,
and a grammar will consist of the list of all relevant productions.

\section{Parsing as effect}
%if style == newcode
\begin{code}
  open Combinations
\end{code}
%endif
While we can follow the traditional development of parsers from nondeterministic state,
algebraic effects allow us to introduce new effects,
which saves us bookkeeping issues.
For a description of parsing based on algebraic effects, we introduce a new effect |EParser|,
and use a state consisting of a |String|.
The |EParser| effect has one command |Parse|, which either returns the current character in the state (advancing it to the next character) or fails if all characters have been consumed.
In our current development, we do not need more commands such as an |EOF| command which succeeds only if all characters have been consumed,
so we do not incorporate them.
However, in the semantics we will define that parsing was successful if the input string has been completely consumed.
\begin{code}
  data CParser : Set where
    Parse : CParser
  RParser : CParser -> Set
  RParser Parse = Char
  EParser = eff CParser RParser

  parse : (Forall(es)) ⦃ iP : EParser ∈ es ⦄ -> Free es Char
  parse ⦃ iP ⦄ = Step iP Parse Pure
\end{code}

Note that |EParse| is not sufficient alone to implement even simple parsers such as |dmatch|:
we need to be able to choose between parsing the next character or returning a value for the empty string.
This is why we usually combine |EParser| with the nondeterminism effect |ENondet|.
However, nondeterminism and parsing is not always enough:
we also need general recursion to deal with productions of the form |E → E|.
% We will show that the three effects together suffice to parse any context-free grammar represented by |Productions|.

The denotational semantics of a parser in the |Free| monad are given by handling the effects.
We give two functions, one returning a |Parser| and one returning a |Trie|.
\begin{code}
  toParser : (Forall(a)) Free (ENondet :: EParser :: Nil) a -> Parser a
  toTrie : (Forall(a)) Free (ENondet :: EParser :: Nil) a -> Trie ∞ a

  toParser (Pure x) Nil = x :: Nil
  toParser (Pure x) (_ :: _) = Nil
  toParser (Step ∈Head Fail k) xs = Nil
  toParser (Step ∈Head Choice k) xs = toParser (k True) xs ++ toParser (k False) xs
  toParser (Step (∈Tail ∈Head) Parse k) Nil = Nil
  toParser (Step (∈Tail ∈Head) Parse k) (x :: xs) = toParser (k x) xs

  toTrie (Pure x) = record { ε = x :: Nil ; d_/d_ = λ _ -> emptyTrie }
  toTrie (Step ∈Head Fail k) = emptyTrie
  toTrie (Step ∈Head Choice k) = toTrie (k True) ∪t toTrie (k False)
  toTrie (Step (∈Tail ∈Head) Parse k) = record { ε = Nil ; d_/d_ = λ x -> toTrie (k x) }
\end{code}
If we prefer to look at the semantics of parsing as a proposition instead of a function,
we can use predicate transformers.
Since the |Parse| effect uses a state consisting of the string to be parsed,
the predicates depend on this state.
We modify the definition of |wp| so each |Effect| can access its own state.
\begin{code}
  record PTS (s : Set) (e : Effect) : Set where
    constructor mkPTS
    field
      pt : (c : Effect.C e) → (Effect.R e c → s → Set) → s → Set
      mono : ∀ c P Q → (∀ x t → P x t → Q x t) → ∀ t → pt c P t → pt c Q t

  data PTSs (s : Set) : List Effect -> Set where
    Nil : PTSs s Nil
    _::_ : ∀ {e es} -> PTS s e -> PTSs s es -> PTSs s (e :: es)

  lookupPTS : ∀ {s C R es} (pts : PTSs s es) (i : eff C R ∈ es) -> (c : C) -> (R c -> s -> Set) -> s -> Set
  lookupPTS (pt :: pts) ∈Head c P t = PTS.pt pt c P t
  lookupPTS (pt :: pts) (∈Tail i) c P t = lookupPTS pts i c P t
  lookupMono : ∀ {s C R es} (pts : PTSs s es) (i : eff C R ∈ es) -> ∀ c P P' → (∀ x t → P x t → P' x t) → ∀ t → lookupPTS pts i c P t → lookupPTS pts i c P' t
  lookupMono (pt :: pts) ∈Head = PTS.mono pt
  lookupMono (pt :: pts) (∈Tail i) = lookupMono pts i

  wp : ∀ {s es a} -> (pts : PTSs s es) -> Free es a -> (a -> s -> Set) -> s -> Set
  wp pts (Pure x) P = P x
  wp pts (Step i c k) P = lookupPTS pts i c (λ x -> wp pts (k x) P)
\end{code}

To give the predicate transformer semantics of the |EParser| effect,
we need to choose the meaning of failure, for the case where the next character is needed
and all characters have already been consumed.
Since we want all results returned by the parser to be correct,
we use demonic choice and the |ptAll| predicate transformer
as the semantics for |ENondet|.
Using |ptAll|'s semantics for the |Fail| command gives the following semantics for the |EParser| effect.
\begin{code}
  ptParse : PTS String EParser
  PTS.pt ptParse Parse P Nil = ⊤
  PTS.pt ptParse Parse P (x :: xs) = P x xs
\end{code}
%if style == newcode
\begin{code}
  PTS.mono ptParse Parse P Q imp Nil asm = tt
  PTS.mono ptParse Parse P Q imp (x :: xs) asm = imp x xs asm
  ptAll : ∀ {s} -> PTS s ENondet
  PTS.pt ptAll Fail P _ = ⊤
  PTS.pt ptAll Choice P s = (P True s) ∧ (P False s)
  PTS.mono ptAll = ?
\end{code}
%endif

\begin{Ex}
With the predicate transformer semantics of |EParse|,
we can define the language accepted by a parser in the |Free| monad as a predicate over strings:
a string |xs| is in the language of a parser |S| if the postcondition ``all characters have been consumed'' is satisfied.
\begin{code}
  empty? : (Forall(a)) List a -> Set
  empty? Nil = ⊤
  empty? (_ :: _) = ⊥

  _∈[_] : (Forall(a)) String -> Free (ENondet :: EParser :: Nil) a -> Set
  xs ∈[ S ] = wp (ptAll :: ptParse :: Nil) S (λ _ -> empty?) xs
\end{code}
\vspace{-2 \baselineskip}
\end{Ex}

\section{From abstract grammars to abstract parsers}
We want to show that the effects |EParser| and |ENondet| are sufficient to parse any context-free grammar,
using a generally recursive function.
To show this claim, we implement a function |fromProductions| that constructs a parser for any context-free grammar given as a list of |Production|s,
then formally verify the correctness of |fromProductions|.
Our implementation mirrors the definition of the |generateParser| function by \citeauthor{dependent-grammar},
differing in the naming and in the system that the parser is written in:
our implementation uses the |Free| monad and algebraic effects, while \citeauthor{dependent-grammar} use a monad |Parser| that is based on parser combinators.
%if style == newcode
\begin{code}
module FromProductions (gs : GrammarSymbols) (prods : Grammar.Productions gs) where
  open GrammarSymbols gs
  open Grammar gs
  open Combinations
\end{code}
%endif

We start by defining two auxiliary types, used as abbreviations in our code.
\begin{code}
  FreeParser = Free (eff Nonterminal ⟦_⟧ :: ENondet :: EParser :: Nil)

  record ProductionRHS (A : Nonterminal) : Set where
    constructor prodrhs
    field
      rhs : Symbols
      sem : ⟦ rhs ∥ A ⟧
\end{code}

The core algorithm for parsing a context-free grammar consists of the following functions,
calling each other in mutual recursion:
\begin{code}
  fromProductions  : (A : Nonterminal) -> FreeParser ⟦ A ⟧
  filterLHS        : (A : Nonterminal) -> Productions -> List (ProductionRHS A)
  fromProduction   : (Forall(A)) ProductionRHS A -> FreeParser ⟦ A ⟧
  buildParser      : (Forall(A)) (xs : Symbols) -> FreeParser (⟦ xs ∥ A ⟧ -> ⟦ A ⟧)
  exact            : (Forall(a)) a -> Char -> FreeParser a
\end{code}
The main function is |fromProductions|: given a nonterminal,
it selects the productions with this nonterminal on the left hand side using |filterLHS|,
and makes a nondeterministic choice between the productions.
\begin{code}
  filterLHS A Nil = Nil
  filterLHS A (prod lhs rhs sem :: ps) with A ≟n lhs
  ... | yes refl  = prodrhs rhs sem :: filterLHS A ps
  ... | no _      = filterLHS A ps

  fromProductions A = foldr (choice (hiddenInstance(∈Tail ∈Head))) (fail (hiddenInstance(∈Tail ∈Head))) (map fromProduction (filterLHS A prods))
\end{code}

The function |fromProduction| takes a single production and tries to parse the input string using this production.
It then uses the semantic function of the production to give the resulting value.
\begin{code}
  fromProduction (prodrhs rhs sem) = buildParser rhs >>= λ f → Pure (f sem)
\end{code}
The function |buildParser| iterates over the |Symbols|, calling |exact| for each literal character symbol,
and making a recursive |call| to |fromProductions| for each nonterminal symbol.
\begin{code}
  buildParser Nil = Pure id
  buildParser (Inl x  :: xs) = exact tt x >>= λ _ -> buildParser xs
  buildParser (Inr B  :: xs) = call B >>= (λ x -> buildParser xs >>= λ o -> Pure λ f -> o (f x))
\end{code}
Finally, |exact| uses the |parse| command to check that the next character in the string is as expected,
and |fail|s if this is not the case.
\begin{code}
  exact x t =
    parse (hiddenInstance(∈Tail (∈Tail ∈Head))) >>= λ t' →
    if' t ≟ t' then (hiddenConst(Pure x)) else (hiddenConst(fail (hiddenInstance(∈Tail ∈Head))))
\end{code}

\section{Partial correctness of the parser}
Partial correctness of the parser is relatively simple to show,
as soon as we have a specification.
Since we want to prove that |fromProductions| correctly parses any given context free grammar given as an element of |Productions|,
the specification consists of a relation between many sets:
the production rules, an input string, a nonterminal, the output of the parser, and the remaining unparsed string.
Due to the many arguments, the notation is unfortunately somewhat unwieldy.
To make it a bit easier to read, we define two relations in mutual recursion,
one for all productions of a nonterminal,
and for matching a string with a single production rule.
%if style == newcode
\begin{code}
module Correctness (gs : GrammarSymbols) where
  open GrammarSymbols gs
  open Grammar gs
  open Combinations
  open FromProductions gs using (FreeParser; fromProductions)

  data _⊢_∈⟦_⟧=>_,_ (prods : Productions) : String -> (A : Nonterminal) -> ⟦ A ⟧ -> String -> Set
  data _⊢_~_=>_,_ (prods : Productions) {A : Nonterminal} : String -> (ps : Symbols) -> (⟦ ps ∥ A ⟧ -> ⟦ A ⟧) -> String -> Set
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
  ptRec : ∀ {a : Set} {I : Set} {O : I -> Set} -> ((i : I) -> a -> O i -> a -> Set) -> PTS a (ERec I O)
  PTS.pt (ptRec R) i P s = ∀ o s' -> R i s o s' -> P o s'
  PTS.mono (ptRec R) = ?

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
  parserSpec : (prods : Productions) (A : Nonterminal) (xs : String) -> ⟦ A ⟧ -> String -> Set
  parserSpec prods A xs o ys = prods ⊢ xs ∈⟦ A ⟧=> o , ys

  pts : Productions -> PTSs (String) _
  wpFromProd : (Forall(a)) (prods : Productions) -> FreeParser prods a -> (a -> String -> Set) -> String -> Set
\end{code}
%endif
With these relations, we can define the specification |parserSpec| to be equal to |_⊢_∈⟦_⟧=>_,_| (up to reordering some arguments),
and show that |fromProductions| refines this specification.
For the semantics of general recursion, we also make use of the specification,
while for the semantics of nondeterminism, we use the |ptAll| semantics to ensure all output is correct.
This gives the partial correctness term as defined below
\begin{code}
  pts prods = ptRec (parserSpec prods) :: ptAll :: ptParse :: Nil

  wpFromProd prods = wp (pts prods)

  partialCorrectness : (prods : Productions) (A : Nonterminal) ->
    wpSpec [[ (hiddenConst(⊤)) , (parserSpec prods A) ]] ⊑ wpFromProd prods (fromProductions prods A)
\end{code}

%if style == newcode
\begin{code}
  consequence : ∀ {a b s es} (pts : PTSs s es) {P} (mx : Free es a) (f : a -> Free es b) ->
    ∀ t -> wp pts mx (λ x t -> wp pts (f x) P t) t == wp pts (mx >>= f) P t
  consequence pts (Pure x) f t = refl
  consequence pts (Step i c k) f t = cong (λ P -> lookupPTS pts i c P t) (extensionality λ x -> extensionality λ t -> consequence pts (k x) f t)

  wpToBind : ∀ {a b s es} (pts : PTSs s es) {P} (mx : Free es a) (f : a -> Free es b) ->
    ∀ t -> wp pts mx (λ x t -> wp pts (f x) P t) t -> wp pts (mx >>= f) P t
  wpToBind pts mx f t H = subst id (consequence pts mx f t) H

  wpFromBind : ∀ {a b s es} (pts : PTSs s es) {P} (mx : Free es a) (f : a -> Free es b) ->
    ∀ t -> wp pts (mx >>= f) P t -> wp pts mx (λ x t -> wp pts (f x) P t) t
  wpFromBind pts mx f t H = subst id (sym (consequence pts mx f t)) H
  partialCorrectness prods A P xs H = ? -- filterStep prods A id P xs H
    where
    open FromProductions gs
\end{code}
%endif
Let us fix the production rules |prods|.
How do we prove the partial correctness?
Since the structure of |fromProductions| is of a nondeterministic choice between productions to be parsed,
and we want to show that all alternatives for a choice result in success,
we will first give a lemma expressing the correctness of each alternative.
Correctness in this case is expressed by the semantics of a single production rule,
i.e. the |_⊢_~_=>_,_| relation.
Thus, we want to prove a lemma with a type as follows:
\begin{code}
    parseStep : ∀ A xs P str ->
      ((o : ⟦ xs ∥ A ⟧ -> ⟦ A ⟧) (str' : String) -> prods ⊢ str ~ xs => o , str' -> P o str') ->
      wpFromProd prods (buildParser prods xs) P str
\end{code}
The lemma can be proved by reproducing the case distinctions used to define |buildParser|;
there is no complication apart from having to use the |fold-bind| lemma to deal with the |_>>=_| operator in a few places.
\begin{code}
    parseStep A Nil P t H = H id t Done
    parseStep A (Inl x :: xs) P Nil H = tt
    parseStep A (Inl x :: xs) P (x' :: t) H with x ≟ x'
    ... | yes refl = parseStep A xs P t λ o t' H' -> H o t' (Next H')
    ... | no ¬p = tt
    parseStep A (Inr B :: xs) P t H = ? -- = λ o t' Ho → subst (hiddenArg(λ f → f t')) (sym (fold-bind (buildParser prods xs) _ P _)) (parseStep A xs _ t' λ o' t'' Ho' → H _ _ (Call Ho Ho'))
\end{code}

To combine the |parseStep| for each of the productions in the nondeterministic choice,
it is tempting to define another lemma |filterStep| by induction on the list of productions.
But we must be careful that the productions that are used in the |parseStep| are the full list |prods|,
not the sublist |prods'| used in the induction step.
Additionally, we must also make sure that |prods'| is indeed a sublist,
since using an incorrect production rule in the |parseStep| will result in an invalid result.
Thus, we parametrise |filterStep| by a list |prods'| and a proof that it is a sublist of |prods|.
Again, the proof uses the same distinction as |fromProductions| does,
and uses the |fold-bind| lemma to deal with the |_>>=_| operator.
\begin{code}
    filterStep : ∀ prods' -> ((Forall(p)) p ∈ prods' -> p ∈ prods) ->
      ∀ A -> wpSpec [[ (hiddenConst(⊤)) , parserSpec prods A ]] ⊑ wpFromProd prods
        (foldr (choice (hiddenInstance(∈Tail ∈Head))) (fail (hiddenInstance(∈Tail ∈Head))) (map (fromProduction prods) (filterLHS prods A prods')))
    filterStep Nil subset A P xs H = tt
    filterStep (prod lhs rhs sem :: prods') subset A P xs H with A ≟n lhs
    filterStep (prod .A rhs sem :: prods') subset A P xs (_ , H) | yes refl
      = ? -- subst (λ f → f xs) (sym (fold-bind (buildParser prods rhs) _ P _))
      (parseStep A rhs _ xs λ o t' H' → H _ _ (Produce (subset ∈Head) H'))
      , filterStep prods' (subset ∘ ∈Tail) A P xs (_ , H)
    ... | no ¬p = filterStep prods' (subset ∘ ∈Tail) A P xs H
\end{code}

With these lemmas, |partialCorrectness| just consists of applying |filterStep| to the subset of |prods| consisting of |prods| itself.

\section{Termination of the parser} \label{sec:fromProductions-terminates}
To show termination we need a somewhat more subtle argument:
since we are able to call the same nonterminal repeatedly,
termination cannot be shown simply by inspecting the definitions.
Consider the grammar given by $E \rightarrow a E; E \rightarrow b$,
where we see that the string that matches $E$ in the recursive case is shorter than the original string,
but the definition itself is of unbounded length.
Fortunately for us, predicate transformer semantics allow us to give this more subtle definition of termination,
in the form of the |Termination| type in Definition \ref{def:variant-termination}.
By taking into account the current state, i.e. the string to be parsed, in the variant,
we can show that a decreasing string length leads to termination.

But not all grammars feature this decreasing string length in the recursive case,
with the most pathological case being those of the form $E \to E$.
The issues do not only occur in edge cases: the grammar $E \to E + E; E \to 1$ representing very simple expressions
will already result in non-termination for |fromProductions|
as it will go in recursion on the first non-terminal without advancing the input string.
Since the position in the string and current nonterminal together fully determine the state of |fromParsers|,
it will not terminate.
We need to ensure that the grammars passed to the parser do not allow for such loops.

Intuitively, the condition on the grammars should be that they are not \introTerm[left recursion]{left-recursive},
since in that case, the parser should always advance its position in the string before it encounters the same nonterminal.
This means that the number of recursive calls to |fromProductions| is bounded
by the length of the string times the number of different nonterminals occurring in the production rules.
The type we will use to describe the predicate ``there is no left recursion'' is constructively somewhat stronger:
we define a left-recursion chain from $A$ to $B$ to be
a sequence of nonterminals $A, \dots, A_i, A_{i+1}, \dots, B$,
such that for each adjacent pair $A_i, A_{i+1}$ in the chain, there is a production of the form $A_{i+1} \to B_1 B_2 \dots B_n A_i \dots$, where $B_1 \dots B_n$ are all nonterminals.
In other words, we can advance the parser to $A$ starting in $B$ without consuming a character.
Disallowing (unbounded) left recursion is not a limitation for our parsers:
\citet{dependent-grammar} have shown that the \introTerm{left-corner transform}
can transform left-recursive grammars into an equivalent grammar without left recursion.
Moreover, they have implemented this transform, including formal verification, in Agda.
In this work, we assume that the left-corner transform has already been applied if needed,
so that there is an upper bound on the length of left-recursive chains in the grammar.

We formalize one link of this left-recursive chain in the type |LeftRec|,
while a list of such links forms the |LeftRecChain| data type.
% Get rid of the implicit fields.
\begin{spec}
  record LeftRec (prods : Productions) (A B : Nonterminal) : Set where
    field
      rec : prod A (map Inr xs ++ (Inr B :: ys)) sem ∈ prods
\end{spec}
(We leave |xs|, |ys| and |sem| as implicit fields of |LeftRec|, since they are fixed by the type of |rec|.)
%if style == newcode
\begin{code}
  record LeftRec (prods : Productions) (A B : Nonterminal) : Set where
    field
      {xs} : List Nonterminal
      {ys} : List Symbol
      {sem} : _
      rec : prod B (map Inr xs ++ (Inr A :: ys)) sem ∈ prods
\end{code}
%endif
\begin{code}
  data LeftRecChain (prods : Productions) : Nonterminal -> Nonterminal -> Set where
    Nil : (Forall(A)) LeftRecChain prods A A
    _::_ : (Forall(A B C)) LeftRec prods B A -> LeftRecChain prods A C -> LeftRecChain prods B C
\end{code}
Now we say that a set of productions has no left recursion if all such chains have an upper bound on their length.
%if style == newcode
\begin{code}
  open import Data.Nat using (_<_; _≤_; _*_; _+_; _∸_; z≤n; s≤s)
  open import Data.Nat.Properties hiding (_≟_)
\end{code}
%endif
\begin{code}
  chainLength : (Forall(prods A B)) LeftRecChain prods A B -> Nat
  chainLength Nil = 0
  chainLength (c :: cs) = Succ (chainLength cs)

  leftRecBound : Productions -> Nat -> Set
  leftRecBound prods n = (Forall(A B)) (cs : LeftRecChain prods A B) -> chainLength cs < n
\end{code}
If we have this bound on left recursion, we are able to prove termination,
since each call to |fromProductions| will be made either after we have consumed an extra character,
or it is a left-recursive step, of which there is an upper bound on the sequence.
Thus, the relation |RecOrder| will work as a recursive \meldTerm{variant} for |fromProductions|:
\begin{code}
  data RecOrder (prods : Productions) : (x y : Nonterminal × String) -> Set where
    Adv : (Forall(str str' A B)) length str < length str' → RecOrder prods (A , str) (B , str')
    Rec : (Forall(str str' A B)) length str ≤ length str' → LeftRec prods A B → RecOrder prods (A , str) (B , str')
\end{code}

\todo{Goede plaats hiervoor?}
The petrol-driven semantics are based on a syntactic argument:
we know a computation terminates because expanding the call tree will eventually result in no more |call|s.
Termination can also be defined based on a well-foundedness argument,
such as the size-change principle of Agda's termination checker.
Thus, we want to say that a recursive definition is \meldTerm{well-founded}
if all recursive calls are made to a smaller argument, according to a well-founded relation.
\begin{Def}[\cite{aczel-acc}]
In intuitionistic type theory, we say that a relation |_≺_| on a type |a| is well-founded if all elements |x : a| are \introTerm{accessible},
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

The condition that all calls are made to a smaller argument is related to the notion of a loop \introTerm{variant}
in imperative languages.
While an \meldTerm{invariant} is a predicate that is true at the start and end of each looping step,
the variant is a relation that holds between successive looping steps.
\begin{Def}
Given a recursive definition |f : RecArr I es O|,
a relation |_≺_| on |C| is a recursive \introTerm{variant} if for each argument |c|,
and each recursive call made to |c'| in the evaluation of |f c|,
we have |c' ≺ c|.
Formally:
\begin{code}
  variant' : (Forall(s es C R a)) (pts : PTSs s (eff C R :: es)) (f : (RecArr C es R)) (_≺_ : (C × s) → (C × s) → Set)
    (c : C) (t : s) (S : Free (eff C R :: es) a) → s → Set
  variant' pts f _≺_ c t (Pure x) t' = ⊤
  variant' pts f _≺_ c t (Step ∈Head c' k) t'
    = ((c' , t') ≺ (c , t)) × lookupPTS pts ∈Head c' (λ x → variant' pts f _≺_ c t (k x)) t'
  variant' pts f _≺_ c t (Step (∈Tail i) c' k) t'
    = lookupPTS pts (∈Tail i) c' (λ x → variant' pts f _≺_ c t (k x)) t'

  variant : (Forall(s es C R)) (pts : PTSs s (eff C R :: es)) (f : (RecArr C es R)) → ((C × s) → (C × s) → Set) → Set
  variant (hidden(s)) (hidden(es)) (hidden(C)) (hidden(R)) pts f _≺_ = ∀ c t → variant' pts f _≺_ c t (f c) t
\end{code}
\end{Def}
Note that |variant| depends on the semantics |pt| we give to |f|.
We cannot derive the semantics in |variant| from the structure of |f|,
since we do not yet know whether |f| terminates.
Using |variant|, we can define another termination condition:
\begin{Def}
A recursive definition |f| is \introTerm[termination!well-founded]{well-founded} if it has a variant that is well-founded.
\begin{code}
  record Termination (hidden(s es C R)) (pts : PTSs s (eff C R :: es)) (f : (RecArr C es R)) : Set where
    field
      _≺_ : (C × s) → (C × s) → Set
      w-f : ∀ c t → Acc _≺_ (c , t)
      var : variant pts f _≺_
\end{code}
\end{Def}
A generally recursive function that terminates in the petrol-driven semantics is also well-founded,
since a variant is given by the well-order |_<_| on the amount of fuel consumed by each call.
The converse also holds: if we have a descending chain of calls |cs| after calling |f| with argument |c|,
we can use induction on the type |Acc _≺_ c| to bound the length of |cs|.
This bound gives the amount of fuel consumed by evaluating a call to |f| on |c|.

With the definition of |RecOrder|, we can complete the correctness proof of |fromProductions|,
by giving an element of the corresponding |Termination| type.
We assume that the length of recursion is bounded by |bound : Nat|.
\begin{code}
  fromProductionsTerminates : (prods : Productions) (bound : Nat) -> leftRecBound prods bound ->
    Termination (pts prods) (fromProductions prods)
  Termination._≺_ (fromProductionsTerminates prods bound H) = RecOrder prods
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
  Termination.w-f (fromProductionsTerminates prods bound H) A str
    = acc (go A str (length str) ≤-refl bound Nil ≤-refl)
    where
    go : (Forall(B)) ∀ A str →
      (k : Nat) → length str ≤ k →
      (n : Nat) (cs : LeftRecChain prods A B) → bound ≤ chainLength cs + n →
      ∀ y → RecOrder prods y (A , str) → Acc (RecOrder prods) y

    go A Nil Zero ltK n cs H' (A' , str') (Adv ())
    go A (_ :: _) Zero () n cs H' (A' , str') (Adv lt)

    go A (_ :: _) (Succ k) (s≤s ltK) n cs H' (A' , str') (Adv (s≤s lt))
      = acc (go A' str' k (≤-trans lt ltK) bound Nil ≤-refl)
    go A str k ltK Zero cs H' (A' , str') (Rec lt cs')
      = magic (<⇒≱ (H cs) (≤-trans H' (≤-reflexive (+-identityʳ _))))
    go A str k ltK (Succ n) cs H' (A' , str') (Rec lt c)
      = acc (go A' str' k (≤-trans lt ltK) n (c :: cs) (≤-trans H' (≤-reflexive (+-suc _ _))))
\end{code}

%if style == newcode
\begin{code}
  Termination.var (fromProductionsTerminates prods bound H) A str = filterStep prods id A str str ≤-refl
    where
    open FromProductions gs prods hiding (fromProductions)

    variant-fmap : ∀ {a b C R s es _≺_ c t t'} (pts : PTSs s (eff C R :: es)) f S {k : a → b} → variant' pts f _≺_ c t S t' → variant' pts f _≺_ c t (S >>= λ x → Pure (k x)) t'
    variant-fmap pts f (Pure x) H = tt
    variant-fmap pts f (Step ∈Head c k) (fst , snd) = fst , lookupMono pts ∈Head c _ _ (λ x t' H' → variant-fmap pts f (k x) H') _ snd
    variant-fmap pts f (Step (∈Tail i) c k) H = lookupMono pts (∈Tail i) c _ _ (λ x t' H' → variant-fmap pts f (k x) H') _ H

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

    nextNonterminal : ∀ {A B Bs xs sem} -> prod A (map Inr Bs ++ (Inr B :: xs)) sem ∈ prods -> prod A (map Inr (Bs ++ (B :: Nil)) ++ xs) (subst (λ xs' -> ⟦ xs' ∥ A ⟧) (map-snoc B Bs xs) sem) ∈ prods
    nextNonterminal {A} {B} {Bs} {xs} {sem} i = subst2 (λ xs' sem' → prod A xs' sem' ∈ prods) (map-snoc B Bs xs) i
\end{code}
%endif

To show that |RecOrder| is a variant for |fromProductions|, we cannot follow the definitions of |fromProductions| as closely as we did for the partial correctness proof.
We need a complicated case distinction to keep track of the left-recursive chain we have followed in the proof.
For this reason, we split the |parseStep| apart into two lemmas |parseStepAdv| and |parseStepRec|, both showing that |buildParser| maintains the variant.
We also use a |filterStep| that calls the correct |parseStep| for each production in the nondeterministic choice.
\begin{code}
    parseStepAdv : ∀ A xs str str' → length str' < length str →
      variant' (pts prods) (fromProductions prods) (RecOrder prods) A str (buildParser (hidden(A = A)) xs) str'
    parseStepRec : ∀ A xs str str' → length str' ≤ length str →
      ∀ ys (hidden(sem)) -> prod A (map Inr ys ++ xs) sem ∈ prods →
      variant' (pts prods) (fromProductions prods) (RecOrder prods) A str (buildParser (hidden(A = A)) xs) str'
    filterStep : ∀ prods' → ((Forall(x)) x ∈ prods' → x ∈ prods) →
      ∀ A str str' → length str' ≤ length str →
      variant' (pts prods) (fromProductions prods) (RecOrder prods) A str
        (foldr (choice (hiddenInstance(∈Tail ∈Head))) (fail (hiddenInstance(∈Tail ∈Head))) (map fromProduction (filterLHS A prods')))
      str'
\end{code}
In the |parseStepAdv|, we deal with the situation that the parser has already consumed at least one character since it was called.
This means we can repeatedly use the |Adv| constructor of |RecOrder| to show the variant holds.
\begin{code}
    parseStepAdv A Nil str str' lt = tt
    parseStepAdv A (Inl x :: xs) str Nil lt = tt
    parseStepAdv A (Inl x :: xs) str (c :: str') lt with x ≟ c
    parseStepAdv A (Inl x :: xs) (_ :: _ :: str) (.x :: str') (s≤s (s≤s lt)) | yes refl
      = parseStepAdv A xs _ _ (s≤s (≤-step lt))
    ... | no ¬p = tt
    parseStepAdv A (Inr B :: xs) str str' lt
      = Adv lt
      , λ o str'' H → variant-fmap (pts prods) (fromProductions prods) (buildParser xs)
        (parseStepAdv A xs str str'' (≤-trans (s≤s (consumeString str' str'' B o H)) lt))
\end{code}
Here, the lemma |variant-fmap| states that the variant holds for a program of the form |S >>= (Pure ∘ f)| if it does for |S|, since the |Pure| part does not make any recursive calls;
the lemma |consumeString str' str'' B| states that the string |str''| is shorter than |str'| if |str''| is the left-over string after matching |str''| with nonterminal |B|.

In the |parseStepRec|, we deal with the situation that the parser has only encountered nonterminals in the current production.
This means that we can use the |Rec| constructor of |RecOrder| to show the variant holds until we consume a character,
after which we call |parseStepAdv| to finish the proof.
\begin{code}
    parseStepRec A Nil str str' lt ys i = tt
    parseStepRec A (Inl x :: xs) str Nil lt ys i = tt
    parseStepRec A (Inl x :: xs) str (c :: str') lt ys i with x ≟ c
    parseStepRec A (Inl x :: xs) (_ :: str) (.x :: str') (s≤s lt) ys i | yes refl
      = parseStepAdv A xs _ _ (s≤s lt)
    ... | no ¬p = tt
    parseStepRec A (Inr B :: xs) str str' lt ys i
      = Rec lt (record { rec = i })
      , λ o str'' H → variant-fmap (pts prods) (fromProductions prods) (buildParser xs)
        (parseStepRec A xs str str'' (≤-trans (consumeString str' str'' B o H) lt)
        (ys ++ (B :: Nil)) (nextNonterminal i))
\end{code}
Apart from the previous lemmas, we make use of |nextNonterminal i|,
which states that the current production starts with the nonterminals |ys ++ (B :: Nil)|.

The lemma |filterStep| shows that the variant holds on all subsets of the production rules,
analogously to the |filterStep| of the partial correctness proof.
It calls |parseStepRec| since the parser only starts consuming characters after it selects a production rule.
\begin{code}
    filterStep Nil A str str' lt subset = tt
    filterStep (prod lhs rhs sem :: prods') subset A str str' lt with A ≟n lhs
    ... | yes refl
      = variant-fmap (pts prods) (fromProductions prods) (buildParser rhs)
        (parseStepRec A rhs str str' lt Nil (subset ∈Head))
        , filterStep prods' (subset ∘ ∈Tail) A str str' lt
    ... | no ¬p = filterStep prods' (subset ∘ ∈Tail) A str str' lt
\end{code}
As for partial correctness, the main proposition consists of applying |filterStep| to the subset of |prods| consisting of |prods| itself.

Having divided the proof into the three lemmas, the remainder is straightforward.
The proofs of the lemmas use induction on the production rule for |parseStepAdv| and |parseStepRec|,
and induction on the list of rules for |filterStep|,
and call each other as indicated.

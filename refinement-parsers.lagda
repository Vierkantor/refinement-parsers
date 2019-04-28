\documentclass{llncs}

%include agda.fmt
%include refinement-parsers.fmt

%include preamble.tex

%if style == newcode
\begin{code}
{-# OPTIONS --type-in-type #-}
open import Prelude
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
\email{\{t.baanen,w.s.swierstra\}@@uu.nl}}
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
  Split : CNondet
RNondet : CNondet -> Set
RNondet Fail = ⊥
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
  fail {a} = Step Fail magic
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
\end{code}

%if style == newcode
\begin{code}
module Nondet where
\end{code}
%endif
\begin{code}
  ptNondet : (c : CNondet) -> (RNondet c -> Set) -> Set
  ptNondet Fail P = ⊤
  ptNondet Split P = P True ∧ P False
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
  wpNondetAll S P = wpFree ptNondet S P
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
open import Data.Char
open import Data.Char.Unsafe using (_≟_)
String = List Char
\end{code}
%endif
To see how we can use the |Free| monad for writing and verifying a parser,
and more specifically how we use the |ENondet| effect for writing
and the |wpNondetAll| semantics for verifying a parser,
we will look at parsing a given regular language.
A regular language can defined using a regular expression,
which we will represent as an element of the |Regex| datatype:
\begin{code}
data Regex : Set where
  Empty : Regex
  Epsilon : Regex
  Singleton : Char -> Regex
  _·_ : Regex -> Regex -> Regex
  _∣_ : Regex -> Regex -> Regex
  _* : Regex -> Regex
  Mark : Nat -> Regex -> Regex
\end{code}
Here, |Empty| is an expression for empty language (which matches no strings at all),
while |Epsilon| is an expression for the language of the empty string (which matches exactly one string: |""|.
We also allow for output in our regular expressions.
The intended semantics of the |Mark| operation are to indicate which branch was taken during matching.
i.e. apart from deciding whether a string is matched by a language, the matcher should also report which markings occurred.
We will represent these contents of the groups as a list, where the first group is the head of the list, the second group is the next element of the list, and so on.
\todo{a good source?}

In Agda, we can represent the semantics of the |Regex| type
by giving a relation between a |Regex| and a |String| on the one hand (the input of the matcher),
and a list of strings on the other hand (the output of the matcher).
If the |Regex| and |String| do not match, there should be no output,
otherwise the output may be any correct contents of the groups.
We give the relation using the following inductive definition:
\begin{code}
data Match : Regex -> String -> List Nat -> Set where
  Epsilon : Match Epsilon Nil Nil
  Singleton : {x : Char} -> Match (Singleton x) (x :: Nil) Nil
  Concat : {l r : Regex} {ys zs : String} {mls mrs : List Nat} -> Match l ys mls -> Match r zs mrs -> Match (l · r) (ys ++ zs) (mls ++ mrs)
  OrLeft : {l r : Regex} {xs : String} {ms : List Nat} -> Match l xs ms -> Match (l ∣ r) xs ms
  OrRight : {l r : Regex} {xs : String} {ms : List Nat} -> Match r xs ms -> Match (l ∣ r) xs ms
  StarNil : {r : Regex} -> Match (r *) Nil Nil
  StarConcat : {r : Regex} {xs : String} {ms : List Nat} -> Match (r · (r *)) xs ms -> Match (r *) xs ms
  Mark : {r : Regex} {xs : String} {m : Nat} {ms : List Nat} -> Match r xs ms -> Match (Mark m r) xs (m :: ms)
\end{code}
Note that there is no constructor for |Match Empty xs ms| for any |xs| or |ms|,
which we interpret as that there is no way to match the |Empty| language with a string |xs|.
Similarly, the only constructor for |Match Epsilon xs ms| is where |xs| is the empty string |Nil|.

Since the definition of |Match| allows for multiple ways that a given |Regex| and |String| may match,
such as in the trivial case where the |Regex| is of the form |r ∣ r|,
and it also has cases where there is no way to match a |Regex| and a |String|,
such as where the |Regex| is |Empty|,
we can immediately predict some parts of the implementation.
Whenever we encounter an expression of the form |l ∣ r|, we |split| nondeterministically between either |l| or |s|.
Similarly, whenever we encounter the |Empty| expression, we immediately |fail|.

The case of concatenation is not as immediately obvious.
One way that we can deal with it is to instead write a matcher that returns the unmatched portion of the string,
and when we have to match a regular expression of the form |l · r| with a string |xs|,
we match |l| with |xs| giving a left over string |ys|, then match |r| with |ys|.
We can do without changing the return values of the matcher,
by nondeterministically splitting the string |xs| into |ys ++ zs|.
That is what we do in a helper function |allSplits|:
\begin{code}
record SplitList {a : Set} (xs : List a) : Set where
  constructor splitList
  field
    lhs : List a
    rhs : List a
    cat : xs == (lhs ++ rhs)

addLHS : ∀ {a} (x : a) (xs : List a) -> SplitList xs -> SplitList (x :: xs)
addLHS x xs spl = splitList (x :: SplitList.lhs spl) (SplitList.rhs spl) (cong (Cons x) (SplitList.cat spl))
\end{code}
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

  allSplits : ∀ {a} -> (xs : List a) -> Free ENondet (SplitList xs)
  allSplits Nil = Pure (splitList Nil Nil refl)
  allSplits (x :: xs) = split
    (Pure (splitList Nil (x :: xs) refl))
    (allSplits xs >>= λ spl -> Pure (addLHS x xs spl))
\end{code}

Armed with this helper function, we can write our first nondeterministic regular expression matcher,
that does a case distinction on the expression and then checks that the string has the correct format.
\begin{code}
  match : (r : Regex) (xs : String) -> Free ENondet (List Nat)
  match Empty xs = fail
  match Epsilon Nil = Pure Nil
  match Epsilon xs@(_ :: _) = fail
  match (Singleton c) Nil = fail
  match (Singleton c) (x :: Nil) with c ≟ x
  match (Singleton c) (.c :: Nil) | yes refl = Pure Nil
  match (Singleton c) (x :: Nil) | no ¬p = fail
  match (Singleton c) xs@(_ :: _ :: _) = fail
  match (l · r) xs = allSplits xs >>=
    λ spl -> match l (SplitList.lhs spl) >>=
    λ ml -> match r (SplitList.rhs spl) >>=
    λ mr -> Pure (ml ++ mr)
  match (l ∣ r) xs = split (match l xs) (match r xs)
  match (Mark n r) xs = match r xs >>= λ ms -> Pure (n :: ms)
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
  hasNo* (Mark n r) = hasNo* r

  pre : (r : Regex) (xs : String) -> Set
  pre r xs = hasNo* r
  post : (r : Regex) (xs : String) -> List Nat -> Set
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
  wpBind post (Step Split k) f (mxHt , mxHf) P postH = wpBind post (k True) f mxHt P postH , wpBind post (k False) f mxHf P postH
\end{code}
This lemma is a specialization of the left compositionality property,
which states that we can refine on the left hand side of a bind.\todo{cite?}

The correctness proof closely matches the structure of |match| (and by extension |allSplits|).
It uses the same recursion on |Regex| as in the definition of |match|.
Since we make use of |allSplits| in the definition, we first give its correctness proof.
\begin{code}
  allSplitsCorrect : ∀ (xs : String) ->
    wpNondetAll (allSplits xs) (λ _ -> ⊤)
  allSplitsCorrect Nil = tt
  allSplitsCorrect (x :: xs) = tt , wpBind (const ⊤) (allSplits xs) _ (allSplitsCorrect xs) _ λ _ _ -> tt
\end{code}
Then, using |wpBind|, we incorporate this correctness proof in the correctness proof of |match|.
Apart from having to introduce |wpBind|, the proof essentially follows automatically from the definitions.
\begin{code}
  pf : ∀ r xs -> wpSpec [[ pre r xs , post r xs ]] ⊑ wpNondetAll (match r xs)
  pf Empty xs P (preH , postH) = tt
  pf Epsilon Nil P (preH , postH) = postH _ Epsilon
  pf Epsilon (x :: xs) P (preH , postH) = tt
  pf (Singleton x) Nil P (preH , postH) = tt
  pf (Singleton x) (c :: Nil) P (preH , postH) with x ≟ c
  pf (Singleton x) (c :: Nil) P (preH , postH) | yes refl = postH _ Singleton
  pf (Singleton x) (c :: Nil) P (preH , postH) | no ¬p = tt
  pf (Singleton x) (_ :: _ :: _) P (preH , postH) = tt
  pf (l · r) xs P ((preL , preR) , postH) =
    wpBind (const ⊤) (allSplits xs) _ (allSplitsCorrect xs) P λ {(splitList ys zs refl) _ ->
    wpBind (Match l ys) (match l ys) _ (pf l ys _ (preL , λ _ -> id)) P λ mls lH ->
    wpBind (Match r zs) (match r zs) _ (pf r zs _ (preR , λ _ -> id)) P λ mrs rH ->
    postH (mls ++ mrs) (Concat lH rH)}
  pf (l ∣ r) xs P ((preL , preR) , postH) =
    pf l xs _ (preL , λ o x -> postH o (OrLeft x)) ,
    pf r xs _ (preR , λ o x -> postH o (OrRight x))
  pf (r *) xs P (() , postH)
  pf (Mark n r) xs P (preH , postH) =
    wpBind (Match r xs) (match r xs) _ (pf r xs _ (preH , λ _ -> id)) _
    λ ms H -> postH _ (Mark H)
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
  >>=-assoc : ∀ {a b c es} (S : Free es a) (f : a -> Free es b) (g : b -> Free es c) ->
    (S >>= f) >>= g == S >>= (λ x -> f x >>= g)
  >>=-assoc (Pure x) f g = refl
  >>=-assoc (Step i c k) f g = cong (Step i c) (extensionality λ x -> >>=-assoc (k x) _ _)
  >>=-Pure : ∀ {a es} (S : Free es a) ->
    S >>= Pure == S
  >>=-Pure (Pure x) = refl
  >>=-Pure (Step i c k) = cong (Step i c) (extensionality λ x -> >>=-Pure (k x))
\end{code}
%endif
We also to make a small modification to the smart constructors for nondeterminism,
since they now need to keep track of their position within a list of effects.
\todo{Use Agda's instance arguments for |iND| and |iRec| instead of explicit arguments? Might make it a bit more straightforward to write code with it, but apparently the solver is not always smart enough to use them...}
\begin{code}
  fail : ∀ {a es} (i : ENondet ∈ es) -> Free es a
  fail {a} iND = Step iND Fail magic
  split : ∀ {a es} (i : ENondet ∈ es) -> Free es a -> Free es a -> Free es a
  split {a} iND S₁ S₂ = Step iND Split λ b -> if b then S₁ else S₂

  call : ∀ {I O es} -> ERec I O ∈ es -> (i : I) -> Free es (O i)
  call iRec i = Step iRec i Pure
\end{code}

Since we want the effects to behave compositionally,
the semantics of the combination of effects should be similarly found in a list of predicate transformers.
The type |List ((c : C) -> (R c -> Set) -> Set)| is not sufficient,
since we need to ensure the types match up.
Using a dependent type we can define a list of predicate transformers for a list of effects:
\begin{code}
module Stateless where
  open Combinations
  open Nondet
  open Spec
\end{code}
\begin{code}
  data PTs : List Effect -> Set where
    Nil : PTs Nil
    _::_ : ∀ {C R es} -> ((c : C) -> (R c -> Set) -> Set) -> PTs es -> PTs (eff C R :: es)
\end{code}

Given a such a list of predicate transformers,
defining the semantics of an effectful program is a straightforward generalization of |wpFree|.
The |Pure| case is identical, and in the |Step| case we find the predicate transformer at the corresponding index to the effect index |i : e ∈ es| using the |lookupPT| helper function.
\begin{code}
  lookupPT : ∀ {C R es} (pts : PTs es) (i : eff C R ∈ es) -> (c : C) -> (R c -> Set) -> Set
  lookupPT (pt :: pts) ∈Head = pt
  lookupPT (pt :: pts) (∈Tail i) = lookupPT pts i
\end{code}
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
For nondeterminism we alread have the predicate transformer |ptNondet|.
However, it is not as easy to give a predicate transformer for general recursion,
since the intended semantics of a recursive call depend
on the function that is being called, i.e. the function that is being defined.

However, if we have a specification of a function of type |(i : I) -> O i|,
for example in terms of a relation of type |(i : I) -> O i -> Set|,
we can define a predicate transformer:
\begin{code}
  ptRec : ∀ {I : Set} {O : I -> Set} -> ((i : I) -> O i -> Set) -> (i : I) -> (O i -> Set) -> Set
  ptRec R i P = ∀ o -> R i o -> P o
\end{code}
For example, the |Match| relation serves as a specification for the |match| function.
If we use |ptRec R| as a predicate transformer to check that a recursive function satisfies the relation |R|,
then we are proving \emph{partial correctness}, since we assume each recursive call terminates according to the relation |R|.

\section{Recursively parsing every regular expression}

Now we are able to handle the Kleene star:

\begin{code}
  allSplits : ∀ {a es} -> (ENondet ∈ es) -> (xs : List a) -> Free es (SplitList xs)
  allSplits i Nil = Pure (splitList Nil Nil refl)
  allSplits i (x :: xs) = split i
    (Pure (splitList Nil (x :: xs) refl))
    (allSplits i xs >>= λ spl -> Pure (addLHS x xs spl))

  match : ∀ {es} -> (ERec (Pair Regex String) (λ _ -> List Nat) ∈ es) -> (ENondet ∈ es) ->
    Pair Regex String -> Free es (List Nat)
  match iRec iND (Empty , xs) = fail iND
  match iRec iND (Epsilon , Nil) = Pure Nil
  match iRec iND (Epsilon , xs@(_ :: _)) = fail iND
  match iRec iND ((Singleton c) , Nil) = fail iND
  match iRec iND ((Singleton c) , (x :: Nil)) with c ≟ x
  match iRec iND ((Singleton c) , (.c :: Nil)) | yes refl = Pure Nil
  match iRec iND ((Singleton c) , (x :: Nil)) | no ¬p = fail iND
  match iRec iND ((Singleton c) , xs@(_ :: _ :: _)) = fail iND
  match iRec iND ((l · r) , xs) = allSplits iND xs >>=
    λ spl -> call iRec (l , SplitList.lhs spl) >>=
    λ ml -> call iRec (r , SplitList.rhs spl) >>=
    λ mr -> Pure (ml ++ mr)
  match iRec iND ((l ∣ r) , xs) = split iND (call iRec (l , xs)) (call iRec (r , xs))
  match iRec iND (Mark n r , xs) = call iRec (r , xs) >>= λ ms -> Pure (n :: ms)
  match iRec iND ((r *) , Nil) = Pure Nil
  match iRec iND ((r *) , xs@(_ :: _)) = call iRec ((r · (r *)) , xs)
\end{code}

The effects we need to use for running |match| are a combination of nondeterminism and general recursion.
As discussed, we first need to give the specification for |match| before we can verify a program that makes use of |match|.
\begin{code}
  matchSpec : Pair Regex String -> List Nat -> Set
  matchSpec (r , xs) ms = Match r xs ms

  wpMatch : ∀ {a} -> Free (ERec (Pair Regex String) (λ _ -> List Nat) :: ENondet :: Nil) a -> (a -> Set) -> Set
  wpMatch = wpFree (ptRec matchSpec :: ptNondet :: Nil)
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
  allSplitsCorrect : ∀ (xs : String) P ->
    (∀ (spl : SplitList xs) -> P spl) ->
    wpMatch (allSplits (∈Tail ∈Head) xs) P
  allSplitsCorrect Nil P H = H _
  allSplitsCorrect (x :: xs) P H = H _ , wpToBind (allSplits (∈Tail ∈Head) xs) _ (allSplitsCorrect xs (P ∘ addLHS x xs) (λ spl -> H (addLHS x xs spl)))
\end{code}
%endif
On the other hand, the correctness proof for |match| needs a bit of tweaking to deal with the difference in the recursive steps.
\begin{code}
  pf : ∀ r,xs -> wpSpec [[ ⊤ , matchSpec r,xs ]] ⊑ wpMatch (match ∈Head (∈Tail ∈Head) r,xs)
  pf (Empty , xs) P (preH , postH) = tt
  pf (Epsilon , Nil) P (preH , postH) = postH _ Epsilon
  pf (Epsilon , (_ :: _)) P (preH , postH) = tt
  pf (Singleton c , Nil) P (preH , postH) = tt
  pf (Singleton c , (x :: Nil)) P (preH , postH) with c ≟ x
  pf (Singleton c , (.c :: Nil)) P (preH , postH) | yes refl = postH _ Singleton
  pf (Singleton c , (x :: Nil)) P (preH , postH) | no ¬p = tt
  pf (Singleton c , (_ :: _ :: _)) P (preH , postH) = tt
  pf ((l · r) , xs) P (preH , postH) = wpToBind (allSplits (∈Tail ∈Head) xs) _
    (allSplitsCorrect xs _ (λ {(splitList lhs rhs refl) mls lH mrs rH -> postH _ (Concat lH rH)}))
  pf ((l ∣ r) , xs) P (preH , postH) = (λ o H -> postH _ (OrLeft H)) , (λ o H -> postH _ (OrRight H))
  pf (Mark n r , xs) P (preH , postH) = λ o H -> postH (n :: o) (Mark H)
\end{code}
Now we are able to prove correctness of |match| on a Kleene star.
\begin{code}
  pf ((r *) , Nil) P (preH , postH) = postH _ StarNil
  pf ((r *) , (x :: xs)) P (preH , postH) = λ o H -> postH _ (StarConcat H)
\end{code}

However, in this proof we do not show termination of the parsing, so it is just a proof of partial correctness.
To prove termination, it is easier to write a new parser that refines the previous implementation.

\section{Termination, using derivatives}
We can use the Brzozowski derivative to advance the regular expression a single character.\cite{Brzozowski}
\begin{code}
  nilConcat : ∀ {l r xs ms} -> Match (l · r) xs ms -> xs == Nil -> Pair (Sigma (List Nat) (Match l Nil)) (Sigma (List Nat) (Match r Nil))
  nilConcat (Concat {ys = Nil} {Nil} ml mr) cat = (_ , ml) , (_ , mr)
  nilConcat (Concat {ys = Nil} {x :: zs} ml mr) ()
  nilConcat (Concat {ys = x :: ys} {zs} ml mr) ()

  ε? : (r : Regex) -> Dec (Sigma (List Nat) (Match r Nil))
  ε? Empty = no λ ()
  ε? Epsilon = yes (Nil , Epsilon)
  ε? (Singleton x) = no λ ()
  ε? (l · r) with ε? l | ε? r
  ε? (l · r) | yes (ml , pl) | yes (mr , pr) = yes ((ml ++ mr) , (Concat pl pr))
  ε? (l · r) | yes pl | no ¬pr = no λ {(m , x) -> ¬pr (Pair.snd (nilConcat x refl))}
  ε? (l · r) | no ¬pl | yes pr = no λ {(m , x) -> ¬pl (Pair.fst (nilConcat x refl))}
  ε? (l · r) | no ¬pl | no ¬pr = no λ {(m , x) -> ¬pl (Pair.fst (nilConcat x refl))}
  ε? (l ∣ r) with ε? l | ε? r
  ε? (l ∣ r) | yes (ml , pl) | yes pr = yes (ml , OrLeft pl)
  ε? (l ∣ r) | yes (ml , pl) | no ¬pr = yes (ml , OrLeft pl)
  ε? (l ∣ r) | no ¬pl | yes (mr , pr) = yes (mr , OrRight pr)
  ε? (l ∣ r) | no ¬pl | no ¬pr = no λ {(ml , OrLeft pl) -> ¬pl (ml , pl) ; (mr , OrRight pr) -> ¬pr (mr , pr)}
  ε? (r *) = yes (Nil , StarNil)
  ε? (Mark n r) with ε? r
  ... | yes (m , p) = yes (_ , Mark p)
  ... | no ¬p = no λ { (m , Mark x) -> ¬p (_ , x) }

  ε-ize : Regex -> Regex
  ε-ize Empty = Empty
  ε-ize Epsilon = Epsilon
  ε-ize (Singleton _) = Empty
  ε-ize (l · r) = ε-ize l · ε-ize r
  ε-ize (l ∣ r) = ε-ize l ∣ ε-ize r
  ε-ize (r *) = Epsilon
  ε-ize (Mark n r) = Mark n (ε-ize r)

  d_/d_ : Regex -> Char -> Regex
  d Empty /d c = Empty
  d Epsilon /d c = Empty
  d Singleton x /d c with c ≟ x
  ... | yes p = Epsilon
  ... | no ¬p = Empty
  d l · r /d c with ε? l
  ... | yes p = ((d l /d c) · r) ∣ (ε-ize l · (d r /d c))
  ... | no ¬p = (d l /d c) · r
  d l ∣ r /d c = (d l /d c) ∣ (d r /d c)
  d r * /d c = (d r /d c) · (r *)
  d Mark n r /d c = Mark n (d r /d c)
\end{code}

When we apply this to matching, we get the function |dmatch|.
\begin{code}
  dmatch : ∀ {es} -> (ERec (Pair Regex String) (λ _ -> List Nat) ∈ es) -> (ENondet ∈ es) ->
    Pair Regex String -> Free es (List Nat)
  dmatch iRec iND (r , Nil) with ε? r
  ... | yes (ms , _) = Pure ms
  ... | no ¬p = fail iND
  dmatch iRec iND (r , (x :: xs)) = call iRec ((d r /d x) , xs)
\end{code}

Since |dmatch| always consumes a character before going in recursion, we can easily prove that each recursive call only leads to finitely many other calls.
This means that for each input value we can unfold the recursive step in the definition a bounded number of times and get a computation with no recursion.
Intuitively, this means that |dmatch| terminates on all input.
If we want to make this more formal, we need to consider what it means to have no recursion in the computation.
A definition for the |while| loop using general recursion looks as follows:
\begin{code}
  while : ∀ {es a} -> (ERec a (K a) ∈ es) -> (a -> Bool) -> (a -> a) -> (a -> Free es a)
  while iRec cond body i = if cond i then Pure i else (call iRec (body i))
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
We formalize this idea in the |termination| predicate.
%if style == newcode
\begin{code}
  ∈-++ : ∀ {a x} {xs ys : List a} -> x ∈ ys -> x ∈ (xs ++ ys)
  ∈-++ {xs = Nil} i = i
  ∈-++ {xs = x :: xs} i = ∈Tail (∈-++ i)

  repeat : ∀ {a : Set} -> Nat -> (a -> a) -> a -> a
  repeat Zero f x = x
  repeat (Succ n) f x = repeat n f (f x) -- or |f (repeat n f x)| ?

  open import Data.Nat using (_+_; _≤_)
\end{code}
%endif
\begin{code}
  data CPartial : Set where
    Fail : CPartial
  RPartial : CPartial -> Set
  RPartial Fail = ⊥
  EPartial = eff CPartial RPartial
  ptPartial : (c : CPartial) -> (RPartial c -> Set) -> Set
  ptPartial Fail _ = ⊥

  unfold : ∀ {I O es a} (f : (i : I) -> Free (ERec I O :: es) (O i)) ->
    (Free (ERec I O :: es) a) -> Nat -> Free (EPartial :: es) a
  unfold f (Pure x) n = Pure x
  unfold f (Step ∈Head c k) Zero = Step ∈Head Fail λ ()
  unfold f (Step ∈Head c k) (Succ n) = unfold f (f c) n >>= λ o -> unfold f (k o) (Succ n)
  unfold f (Step (∈Tail i) c k) n = Step (∈Tail i) c λ o -> unfold f (k o) n

  terminates-in : ∀ {I O a es} (pts : PTs es) (f : (i : I) -> Free (ERec I O :: es) (O i)) ->
    Free (ERec I O :: es) a -> Nat -> Set
  terminates-in pts f S n = wpFree (ptPartial :: pts) (unfold f S n) (λ _ -> ⊤)

  termination : ∀ {I O es} (pts : PTs es) (f : (i : I) -> Free (ERec I O :: es) (O i)) -> Set
  termination pts f = ∀ i -> Sigma Nat (terminates-in pts f (f i))
\end{code}

To show that |dmatch| actually terminates, we need two small helper lemmas.
\begin{code}
  terminates-call : ∀ {I O es} pts (f : (i : I) -> Free (ERec I O :: es) (O i)) ->
    (i : I) (n : Nat) ->
    terminates-in pts f (f i) n -> terminates-in pts f (call ∈Head i) (Succ n)
  terminates-call pts f i n t = subst (λ S -> wpFree _ S _) (sym (>>=-Pure (unfold f (f i) n))) t

  dmatch-terminates : termination (ptNondet :: Nil) (dmatch ∈Head (∈Tail ∈Head))
  dmatch-terminates (r , xs) = Succ (length xs) , lemma r xs
    where
    lemma : ∀ r xs -> terminates-in (ptNondet :: Nil) (dmatch ∈Head (∈Tail ∈Head)) (dmatch ∈Head (∈Tail ∈Head) (r , xs)) (Succ (length xs))
    lemma r Nil with ε? r
    lemma r Nil | yes p = tt
    lemma r Nil | no ¬p = tt
    lemma r (x :: xs) = terminates-call (ptNondet :: Nil) (dmatch _ _) ((d r /d x) , xs) (Succ (length xs)) (lemma (d r /d x) xs)
\end{code}

Moreover, |dmatch| is a refinement of |match|, which means it is also correct.
First we show that |d r /d x| matches strings |xs| such that |r| matches |x :: xs|.
\begin{code}
  ε-izeGivesEpsilon : ∀ r xs ms -> Match (ε-ize r) xs ms -> xs == Nil
  ε-izeGivesEpsilon Empty xs ms ()
  ε-izeGivesEpsilon Epsilon .Nil .Nil Epsilon = refl
  ε-izeGivesEpsilon (Singleton x) xs ms ()
  ε-izeGivesEpsilon (l · r) xs ms (Concat Hl Hr) with ε-izeGivesEpsilon _ _ _ Hl | ε-izeGivesEpsilon _ _ _ Hr
  ... | refl | refl = refl
  ε-izeGivesEpsilon (l ∣ r) xs ms (OrLeft H) = ε-izeGivesEpsilon _ _ _ H
  ε-izeGivesEpsilon (l ∣ r) xs ms (OrRight H) = ε-izeGivesEpsilon _ _ _ H
  ε-izeGivesEpsilon (r *) .Nil .Nil Epsilon = refl
  ε-izeGivesEpsilon (Mark x r) xs .(x :: _) (Mark H) = ε-izeGivesEpsilon _ _ _ H

  ε-izeCorrect : ∀ r xs ms -> Match (ε-ize r) xs ms -> Match r Nil ms
  ε-izeCorrect Empty xs ms ()
  ε-izeCorrect Epsilon .Nil .Nil Epsilon = Epsilon
  ε-izeCorrect (Singleton x) xs ms ()
  ε-izeCorrect (l · r) xs ms (Concat Hl Hr) = Concat (ε-izeCorrect _ _ _ Hl) (ε-izeCorrect _ _ _ Hr)
  ε-izeCorrect (l ∣ r) xs ms (OrLeft H) = OrLeft (ε-izeCorrect _ _ _ H)
  ε-izeCorrect (l ∣ r) xs ms (OrRight H) = OrRight (ε-izeCorrect _ _ _ H)
  ε-izeCorrect (r *) .Nil .Nil Epsilon = StarNil
  ε-izeCorrect (Mark n r) xs .(n :: _) (Mark H) = Mark (ε-izeCorrect _ _ _ H)

  derivativeCorrect : ∀ r x xs ms -> Match (d r /d x) xs ms -> Match r (x :: xs) ms
  derivativeCorrect Empty x xs ms ()
  derivativeCorrect Epsilon x xs ms ()
  derivativeCorrect (Singleton c) x xs ms m with x ≟ c
  derivativeCorrect (Singleton c) .c .Nil .Nil Epsilon | yes refl = Singleton
  derivativeCorrect (Singleton c) x xs ms () | no ¬p
  derivativeCorrect (l · r) x xs ms m with ε? l
  derivativeCorrect (l · r) x xs ms (OrLeft (Concat ml mr)) | yes (mlr , plr) = Concat (derivativeCorrect _ _ _ _ ml) mr
  derivativeCorrect (l · r) x xs ms (OrRight (Concat ml mr)) | yes (mlr , plr) with ε-izeGivesEpsilon _ _ _ ml
  derivativeCorrect (l · r) x xs ms (OrRight (Concat ml mr)) | yes (mlr , plr) | refl = Concat (ε-izeCorrect _ _ _ ml) (derivativeCorrect _ _ _ _ mr)
  derivativeCorrect (l · r) x xs ms (Concat ml mr) | no ¬p = Concat (derivativeCorrect _ _ _ _ ml) mr
  derivativeCorrect (l ∣ r) x xs ms (OrLeft m) = OrLeft (derivativeCorrect _ _ _ _ m)
  derivativeCorrect (l ∣ r) x xs ms (OrRight m) = OrRight (derivativeCorrect _ _ _ _ m)
  derivativeCorrect (r *) x xs ms (Concat ml mr) = StarConcat (Concat (derivativeCorrect _ _ _ _ ml) mr)
  derivativeCorrect (Mark n r) x xs .(n :: _) (Mark m) = Mark (derivativeCorrect _ _ _ _ m)
\end{code}

\begin{code}
  refinement : ∀ r xs -> wpMatch (match ∈Head (∈Tail ∈Head) (r , xs)) ⊑ wpMatch (dmatch ∈Head (∈Tail ∈Head) (r , xs))
  refinement Empty Nil P H = tt
  refinement Empty (x :: xs) P H = λ o ()
  refinement Epsilon Nil P H = H
  refinement Epsilon (x :: xs) P H = λ o ()
  refinement (Singleton c) Nil P H = H
  refinement (Singleton c) (x :: xs) P H with x ≟ c
  refinement (Singleton c) (.c :: Nil) P H | yes refl with c ≟ c
  refinement (Singleton c) (.c :: Nil) P H | yes refl | yes refl = λ {o Epsilon -> H}
  refinement (Singleton c) (.c :: Nil) P H | yes refl | no ¬p = magic (¬p refl)
  refinement (Singleton c) (.c :: _ :: _) P H | yes refl = λ o ()
  refinement (Singleton c) (_ :: _) P H | no ¬p = λ o ()
  refinement (l · r) Nil P H with ε? l | ε? r
  refinement (l · r) Nil P H | yes (ml , pl) | yes (mr , pr) = H _ pl _ pr
  refinement (l · r) Nil P H | yes (ml , pl) | no ¬pr = tt
  refinement (l · r) Nil P H | no ¬pl | yes (mr , pr) = tt
  refinement (l · r) Nil P H | no ¬pl | no ¬pr = tt
  refinement (l · r) (x :: xs) P (fst , snd) o H with ε? l
  refinement (l · r) (x :: xs) P (fst , snd) o (OrLeft (Concat {ys = ys} {zs} Hl Hr)) | yes p = {!consequence (allSplits (∈Tail ∈Head) (x :: xs)) _!}
  refinement (l · r) (x :: xs) P (fst , snd) o (OrRight (Concat Hl Hr)) | yes p with ε-izeGivesEpsilon _ _ _ Hl
  ... | refl = fst _ (ε-izeCorrect _ _ _ Hl) _ (derivativeCorrect _ _ _ _ Hr)
  refinement (l · r) (x :: xs) P (fst , snd) o (Concat Hl H2) | no ¬p = {!allSplitsCorrect!}
  refinement (l ∣ r) Nil P (fst , snd) with ε? l | ε? r
  refinement (l ∣ r) Nil P (fst , snd) | yes (ml , pl) | yes (mr , pr) = fst ml pl
  refinement (l ∣ r) Nil P (fst , snd) | yes (ml , pl) | no ¬pr = fst ml pl
  refinement (l ∣ r) Nil P (fst , snd) | no ¬pl | yes (mr , pr) = snd mr pr
  refinement (l ∣ r) Nil P (fst , snd) | no ¬pl | no ¬pr = tt
  refinement (l ∣ r) (x :: xs) P (fst , snd) = λ { o (OrLeft H) -> fst o (derivativeCorrect _ _ _ _ H) ; o (OrRight H) -> snd o (derivativeCorrect _ _ _ _ H)}
  refinement (r *) Nil P H = H
  refinement (r *) (x :: xs) P H = λ {ms (Concat ml mr) -> H _ (Concat (derivativeCorrect _ _ _ _ ml) mr)}
  refinement (Mark n r) Nil P H with ε? r
  ... | yes (fst , snd) = H _ snd
  ... | no ¬p = tt
  refinement (Mark n r) (x :: xs) P H = λ {o (Mark m) -> H _ (derivativeCorrect r _ _ _ m)}
\end{code}

\section{Different viewpoints of grammars}
In classical logic, a language is no more than a set of strings, or a predicate over strings: |String -> Set|.
Constructively, such predicates (even when decidable) are not very useful: the language $\{xs \mid xs \text{is a valid proof of the Riemann Hypothesis} \}$ has no defined cardinality.
To make them more amenable to reasoning, we impose structure on languages, for example by giving their definition as a regular expression.
For more complicated grammars than regular expressions, we will use the abstract representation of grammars by Kasper Brink.

%if style == newcode
\begin{code}
open import Relation.Binary
\end{code}
%endif
\begin{code}
record GrammarSymbols : Set where
  field
    Terminal : Set
    Nonterminal : Set
    ⟦_⟧ : Nonterminal -> Set
    _≟t_ : Decidable {A = Terminal} _==_
    _≟n_ : Decidable {A = Nonterminal} _==_
module Grammar (gs : GrammarSymbols) where
  open GrammarSymbols gs
  Symbol = Either Terminal Nonterminal
  Symbols = List Symbol
  ⟦_∥_⟧ : Symbols -> Nonterminal -> Set
  ⟦ Nil ∥ A ⟧ = ⟦ A ⟧
  ⟦ Inl x :: xs ∥ A ⟧ = ⟦ xs ∥ A ⟧
  ⟦ Inr B :: xs ∥ A ⟧ = ⟦ B ⟧ -> ⟦ xs ∥ A ⟧
  record Production : Set where
    constructor prod
    field
      lhs : Nonterminal
      rhs : Symbols
      sem : ⟦ rhs ∥ lhs ⟧
  Productions = List Production
\end{code}

Alternatively, we can use the Brzozowski derivative to ensure we can step though the symbols of the language,
so we get the coinductive trie of Andeas Abel:
\begin{code}
  open import Size
  record Trie (i : Size) (a : Set) : Set where
    coinductive
    field
      ε : List a
      d_/d_ : {j : Size< i} -> Terminal -> Trie j a
  open Trie
\end{code}
The field |ε| represents the successful parses of the empty string,
while |d_/d_| gives the subtries after parsing a single |terminal|.
For example, we have the trie for an empty language,
and we can take the union of two tries to get the union of two languages.
\begin{code}
  emptyTrie : ∀ {i a} -> Trie i a
  ε emptyTrie = Nil
  d emptyTrie /d x = emptyTrie

  _∪t_ : ∀ {i a} -> Trie i a -> Trie i a -> Trie i a
  ε (t ∪t t') = ε t ++ ε t'
  d t ∪t t' /d x = (d t /d x) ∪t (d t' /d x)
\end{code}

Our last viewpoint of grammar is a much more computational one: the list-of-succesful-parses type.
\begin{code}
  Parser : Set -> Set
  Parser a = List Terminal -> List a
\end{code}

To unify these different viewpoints, we will apply algebraic effects.

\section{Parsing as effect}
%if style == newcode
\begin{code}
  open Combinations
\end{code}
%endif
While we can follow the traditional development of parsers from nondeterministic state,
algebraic effects allow us to introduce new effects,
which saves us bookkeeping issues.
The |EParser| effect has one commands, which either takes the first character from the input string or fails on an empty string.
In the semantics we will define that the parsing was succesful if the input string is be completely parsed,
so we do not need an effect corresponding to the |eof| parser combinator.
\begin{code}
  data CParser : Set where
    Parse : CParser
  RParser : CParser -> Set
  RParser Parse = Terminal
  EParser = eff CParser RParser

  parse : ∀ {es} -> EParser ∈ es -> Free es Terminal
  parse iP = Step iP Parse Pure
\end{code}

Combining the effects of |EParse| and |ENondet| gives us an abstract representation of the |Parser| type,
where combinators such as nondeterministic choice and sequencing are represented explicitly.
We will show that these effects, together with general recursion,
suffice to parse any abstract grammar.
First of all, we can translate any abstract parser to a parser function,
using suitable handlers for the effects:
\begin{code}
  FreeParser = Free (ENondet :: EParser :: Nil)

  toParser : ∀ {a} -> FreeParser a -> Parser a
  toParser (Pure x) Nil = [ x ]
  toParser (Pure x) (_ :: _) = Nil
  toParser (Step ∈Head Fail k) xs = Nil
  toParser (Step ∈Head Split k) xs = toParser (k True) xs ++ toParser (k False) xs
  toParser (Step (∈Tail ∈Head) Parse k) Nil = Nil
  toParser (Step (∈Tail ∈Head) Parse k) (x :: xs) = toParser (k x) xs
\end{code}
The trie corresponding to the language of an abstract parser is similarly easy to define:
\begin{code}
  toTrie : ∀ {a} -> FreeParser a -> Trie ∞ a
  toTrie (Pure x) = record { ε = [ x ] ; d_/d_ = λ _ -> emptyTrie }
  toTrie (Step ∈Head Fail k) = emptyTrie
  toTrie (Step ∈Head Split k) = toTrie (k True) ∪t toTrie (k False)
  toTrie (Step (∈Tail ∈Head) Parse k) = record { ε = Nil ; d_/d_ = λ x -> toTrie (k x) }
\end{code}

If we prefer to look at the semantics of parsing as a proposition instead of a function,
we can use predicate transformers.
Since the |Parse| effect uses a state consisting of the string to be parsed,
the predicates depend on this state.
We modify the definition of |wp| so each |Effect| can access its own state.
\begin{code}
  data StatePTs (s : Set) : List Effect -> Set where
    Nil : StatePTs s Nil
    _::_ : ∀ {C R es} -> ((c : C) -> (R c -> s -> Set) -> s -> Set) -> StatePTs s es -> StatePTs s (eff C R :: es)

  lookupStatePT : ∀ {s C R es} (pts : StatePTs s es) (i : eff C R ∈ es) -> (c : C) -> (R c -> s -> Set) -> s -> Set
  lookupStatePT (pt :: pts) ∈Head c P t = pt c P t
  lookupStatePT (pt :: pts) (∈Tail i) c P t = lookupStatePT pts i c P t

  wp : ∀ {s es a} -> (pts : StatePTs s es) -> Free es a -> (a -> s -> Set) -> s -> Set
  wp pts (Pure x) P = P x
  wp pts (Step i c k) P = lookupStatePT pts i c (λ x -> wp pts (k x) P)
\end{code}

The predicate transformers corresponding to a single effect become:
\begin{code}
  ptParse : (c : CParser) -> (RParser c -> List Terminal -> Set) -> List Terminal -> Set
  ptParse Parse P Nil = ⊤
  ptParse Parse P (x :: xs) = P x xs
  ptNondet : ∀ {a : Set} -> (c : CNondet) -> (RNondet c -> a -> Set) -> a -> Set
  ptNondet Fail P _ = ⊤
  ptNondet Split P s = (P True s) ∧ (P False s)
\end{code}

This allows us to define the language of an abstract parser: all strings such that the postcondition ``the unmatched string is empty'' is satisfied.
\begin{code}
  empty? : ∀ {a} -> List a -> Set
  empty? Nil = ⊤
  empty? (_ :: _) = ⊥

  _∈[_] : ∀ {a} -> List Terminal -> FreeParser a -> Set
  xs ∈[ S ] = wp (ptNondet :: ptParse :: Nil) S (λ _ -> empty?) xs
\end{code}

\section{From abstract grammars to abstract parsers}
This type of abstract parsers suffices to parse a language given by production rules,
as we will show by generating an abstract parser from a list |Production| rules.
The approach is equivalent to the |generateParser| function by Kasper Brink. % TODO:cite
However, nondeterminism and parsing is not enough: we also need general recursion to deal with definitions such as $E \to E$.
\begin{code}
module FromProductions (gs : GrammarSymbols) (prods : Grammar.Productions gs) where
  open GrammarSymbols gs
  open Grammar gs
  open Combinations

  record ProductionRHS (A : Nonterminal) : Set where
    constructor prodrhs
    field
      rhs : Symbols
      sem : ⟦ rhs ∥ A ⟧

  buildParser : {A : Nonterminal} -> (xs : Symbols) -> Free (ERec Nonterminal ⟦_⟧ :: ENondet :: EParser :: Nil) (⟦ xs ∥ A ⟧ -> ⟦ A ⟧)
  exact : ∀ {a} -> a -> Terminal -> Free (ERec Nonterminal ⟦_⟧ :: ENondet :: EParser :: Nil) a
  filterLHS : (A : Nonterminal) -> Productions -> List (ProductionRHS A)
  fromProduction : {A : Nonterminal} -> ProductionRHS A -> Free (ERec Nonterminal ⟦_⟧ :: ENondet :: EParser :: Nil) ⟦ A ⟧
  fromProductions : (A : Nonterminal) -> Free (ERec Nonterminal ⟦_⟧ :: ENondet :: EParser :: Nil) ⟦ A ⟧

  filterLHS A Nil = Nil
  filterLHS A (prod lhs rhs sem :: ps) with A ≟n lhs
  ... | yes refl = prodrhs rhs sem :: filterLHS A ps
  ... | no _ = filterLHS A ps

  exact x t = parse (∈Tail (∈Tail ∈Head)) >>= λ t' -> if' t ≟t t' then (λ _ -> Pure x) else λ _ -> fail (∈Tail ∈Head)

  buildParser Nil = Pure id
  buildParser (Inl x :: xs) = exact tt x >>= λ _ -> buildParser xs
  buildParser (Inr B :: xs) = call ∈Head B >>= (λ x -> buildParser xs >>= λ o -> Pure λ f -> o (f x))

  fromProduction (prodrhs rhs sem) = buildParser rhs >>= λ f -> Pure (f sem)

  fromProductions A = foldr (split (∈Tail ∈Head)) (fail (∈Tail ∈Head)) (map fromProduction (filterLHS A prods))
\end{code}

Partial correctness is relatively simple to show as soon as we define the semantics of grammars.
For ease of notation, we define two relations mutually recursively,
one for all productions of a nonterminal,
and for matching a string with a single production rule.
\begin{code}
module Correctness (gs : GrammarSymbols) where
  open GrammarSymbols gs
  open Grammar gs
  open Combinations

  data _⊢_∈⟦_⟧=>_,_ (prods : Productions) : List Terminal -> (A : Nonterminal) -> ⟦ A ⟧ -> List Terminal -> Set
  data _⊢_~_=>_,_ (prods : Productions) {A : Nonterminal} : List Terminal -> (ps : Symbols) -> (⟦ ps ∥ A ⟧ -> ⟦ A ⟧) -> List Terminal -> Set

  data _⊢_∈⟦_⟧=>_,_ prods where
    Produce : ∀ {lhs rhs sem xs ys f} -> prod lhs rhs sem ∈ prods -> prods ⊢ xs ~ rhs => f , ys -> prods ⊢ xs ∈⟦ lhs ⟧=> f sem , ys
  data _⊢_~_=>_,_ prods where
    Done : ∀ {xs} -> prods ⊢ xs ~ Nil => id , xs
    Next : ∀ {x xs ys ps o} -> prods ⊢ xs ~ ps => o , ys -> prods ⊢ (x :: xs) ~ (Inl x :: ps) => o , ys
    Call : ∀ {A ps xs ys zs f o} -> prods ⊢ xs ∈⟦ A ⟧=> o , ys -> prods ⊢ ys ~ ps => f , zs -> prods ⊢ xs ~ (Inr A :: ps) => (λ g -> f (g o)) , zs
\end{code}

%if style == newcode
\begin{code}
  ptRec : ∀ {a : Set} {I : Set} {O : I -> Set} -> ((i : I) -> a -> O i -> a -> Set) -> (i : I) -> (O i -> a -> Set) -> a -> Set
  ptRec R i P s = ∀ o s' -> R i s o s' -> P o s'

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

\begin{code}
  spec : Productions -> (A : Nonterminal) -> List Terminal -> ⟦ A ⟧ -> List Terminal -> Set
  spec prods A xs o ys = prods ⊢ xs ∈⟦ A ⟧=> o , ys
  spec' : Productions -> (A : Nonterminal) (xs : List Symbol) -> List Terminal -> (⟦ xs ∥ A ⟧ -> ⟦ A ⟧) -> List Terminal -> Set
  spec' prods A xs t o ys = prods ⊢ t ~ xs => o , ys
  wpFromProd : ∀ {a} -> (prod : Productions) -> Free (ERec Nonterminal ⟦_⟧ :: ENondet :: EParser :: Nil) a -> (a -> List Terminal -> Set) -> List Terminal -> Set
  wpFromProd prods = wp (ptRec (spec prods) :: ptNondet :: ptParse :: Nil)

  consequence : ∀ {a b s es} (pts : StatePTs s es) {P} (mx : Free es a) (f : a -> Free es b) ->
    ∀ t -> wp pts mx (λ x t -> wp pts (f x) P t) t == wp pts (mx >>= f) P t
  consequence pts (Pure x) f t = refl
  consequence pts (Step i c k) f t = cong (λ P -> lookupStatePT pts i c P t) (extensionality λ x -> extensionality λ t -> consequence pts (k x) f t)

  wpToBind : ∀ {a b s es} (pts : StatePTs s es) {P} (mx : Free es a) (f : a -> Free es b) ->
    ∀ t -> wp pts mx (λ x t -> wp pts (f x) P t) t -> wp pts (mx >>= f) P t
  wpToBind pts mx f t H = subst id (consequence pts mx f t) H

  wpFromBind : ∀ {a b s es} (pts : StatePTs s es) {P} (mx : Free es a) (f : a -> Free es b) ->
    ∀ t -> wp pts (mx >>= f) P t -> wp pts mx (λ x t -> wp pts (f x) P t) t
  wpFromBind pts mx f t H = subst id (sym (consequence pts mx f t)) H

  partialCorrectness : (prods : Productions) (A : Nonterminal) ->
    wpSpec [[ (λ _ -> ⊤) , spec prods A ]] ⊑ wpFromProd prods (FromProductions.fromProductions gs prods A)
  partialCorrectness prods A P xs H = filterStep prods A id P xs H
    where
    open FromProductions gs
    lemma : (A : Nonterminal) (xs : Symbols) (P : (⟦ xs ∥ A ⟧ -> ⟦ A ⟧) -> List Terminal -> Set) (t : List Terminal) ->
      ((o : ⟦ xs ∥ A ⟧ -> ⟦ A ⟧) (t' : List Terminal) -> prods ⊢ t ~ xs => o , t' -> P o t') ->
      wpFromProd prods (buildParser prods xs) P t
    lemma A Nil P t H = H id t Done
    lemma A (Inl x :: xs) P Nil H = tt
    lemma A (Inl x :: xs) P (x' :: t) H with x ≟t x'
    ... | yes refl = lemma A xs P t λ o t' H' -> H o t' (Next H')
    ... | no ¬p = tt
    lemma A (Inr B :: xs) P t H = wpToBind (ptRec _ :: _) (call ∈Head B) (λ x -> buildParser prods xs >>= λ o -> Pure λ f -> o (f x)) t
      λ x s' Hcall -> wpToBind _ (buildParser prods xs) _ s'
      (lemma A xs (λ o t' -> P (λ f -> o (f x)) t') s' λ o t' H' -> H (λ f -> o (f x)) t' (Call Hcall H'))

    filterStep : (prods' : Productions) (A : Nonterminal) ->
      (∀ {p} -> p ∈ prods' -> p ∈ prods) ->
      wpSpec [[ (λ _ -> ⊤) , spec prods A ]] ⊑ wpFromProd prods (foldr (split (∈Tail ∈Head)) (fail (∈Tail ∈Head)) (map (fromProduction prods) (filterLHS prods A prods')))
    filterStep Nil A i P xs H = tt
    filterStep (prod lhs rhs sem :: prods') A i P xs H with A ≟n lhs
    filterStep (prod .A rhs sem :: prods') A i P xs (_ , H) | yes refl = wpToBind _ (buildParser prods rhs) _ xs
      (lemma A rhs (λ f -> P (f sem)) xs
        λ o t' H' -> H (o sem) t' (Produce (i ∈Head) H')) ,
      filterStep prods' A (i ∘ ∈Tail) P xs (_ , H)
    ... | no ¬p = filterStep prods' A (i ∘ ∈Tail) P xs H
\end{code}

Termination is somewhat more subtle: since we call the same nonterminal repeatedly,
we cannot get rid of all recursion after enough substitutions of the definition.
Consider the grammar given by $E \rightarrow a E \mid b$,
where we see that the string that matches $E$ in the recursive case is shorter than the original string.
Fortunately for us, predicate transformer semantics give a more subtle definition of termination.
The |terminates-in| predicate defined above says that making the recursive calls fail after enough substitutions
should give identical behaviour to the original program.
Still, this is not sufficient to show that all grammars have a terminating parser:
a language of degenerate grammars such as given by $E \rightarrow E$ is not well-defined.

Intuitively, the condition on the grammars should be that they are not left-recursive,
since in that case, the parser should always advance its position in the string before it encounters the same non-terminal.
This means that the number of recursive calls to |fromProductions| is bounded
by the length of the string times the number of different nonterminals occuring in the production rules.
The type we will use to describe the predicate ``there is no left recursion'' is constructively somewhat stronger:
we define a left-recursion chain to be a sequence of nonterminals $\{A_i\}$ such that $A_{i+1}$ occurs before a terminal in a production of $A_i$.
\begin{code}
  data LeftRecChain : Productions -> Nonterminal -> Set where
    Nil : ∀ {prods A} -> LeftRecChain prods A
    _::_ : ∀ {prods A} {xs : List Nonterminal} {B : Nonterminal} {ys sem} -> prod A (map Inr xs ++ (Inr B :: ys)) sem ∈ prods -> LeftRecChain prods A -> LeftRecChain prods B
\end{code}
And then we say that a set of productions has no left recursion if all such chains have an upper bound on their length.
%if style == newcode
\begin{code}
  open import Data.Nat
  open import Data.Nat.Properties
\end{code}
%endif
\begin{code}
  chainLength : ∀ {prods A} -> LeftRecChain prods A -> Nat
  chainLength Nil = 0
  chainLength (c :: cs) = Succ (chainLength cs)

  leftRecBound : Productions -> Nat -> Set
  leftRecBound prods n = ∀ {A} -> (cs : LeftRecChain prods A) -> chainLength cs < n
\end{code}
%if style == newcode
\begin{code}
  data CPartial : Set where
    Fail : CPartial
  RPartial : CPartial -> Set
  RPartial Fail = ⊥
  EPartial = eff CPartial RPartial
  ptPartial : ∀ {s : Set} -> (c : CPartial) -> (RPartial c -> s -> Set) -> s -> Set
  ptPartial Fail _ _ = ⊥

  unfold : ∀ {I O es a} (f : (i : I) -> Free (ERec I O :: es) (O i)) ->
    (Free (ERec I O :: es) a) -> Nat -> Free (EPartial :: es) a
  unfold f (Pure x) n = Pure x
  unfold f (Step ∈Head c k) Zero = Step ∈Head Fail λ ()
  unfold f (Step ∈Head c k) (Succ n) = unfold f (f c) n >>= λ o -> unfold f (k o) (Succ n)
  unfold f (Step (∈Tail i) c k) n = Step (∈Tail i) c λ o -> unfold f (k o) n

  terminates-in : ∀ {I O a s es} (pts : StatePTs s es) (f : (i : I) -> Free (ERec I O :: es) (O i)) ->
    Free (ERec I O :: es) a -> s -> Nat -> Set
  terminates-in pts f S t n = wp (ptPartial :: pts) (unfold f S n) (λ _ _ -> ⊤) t

  termination : ∀ {I O s es} (pts : StatePTs s es) (f : (i : I) -> Free (ERec I O :: es) (O i)) -> Set
  termination pts f = ∀ i t -> Sigma Nat (terminates-in pts f (f i) t)
\end{code}
%endif
\begin{code}
  fromProductionsTerminates : ∀ (prods : Productions) ->
    (bound : Nat) -> leftRecBound prods bound ->
    termination (ptNondet :: ptParse :: Nil) (FromProductions.fromProductions gs prods)
  fromProductionsTerminates prods bound H A str =
    let n = Succ (length str * bound) + bound
    in n , wp-monotone (unfold fromProductions (fromProductions A) _) str (λ _ _ _ -> tt) (filterStep A str n Nil ≤-refl)
    where
    open FromProductions gs prods

    parseStep : ∀ {prods A str x str'} -> spec prods A str x str' -> length str' ≤ length str
    parseRelStep : ∀ {A prods str rhs} {f : ⟦ rhs ∥ A ⟧ -> ⟦ A ⟧} {str'} -> prods ⊢ str ~ rhs => f , str' -> length str' ≤ length str
    parseRelStep Done = ≤-refl
    parseRelStep (Next H) = ≤-step (parseRelStep H)
    parseRelStep (Call Hc H) = ≤-trans (parseRelStep H) (parseStep Hc)
    parseStep (Produce i H) = parseRelStep H

    -- we have only encountered nonterminals in building this production
    firstBuildingStep : ∀ {A} str n (cs : LeftRecChain prods A) -> Succ (length str * bound + bound ∸ chainLength cs) ≤ n ->
      ∀ Bs (xs : Symbols) {sem} (i : prod A (map Inr Bs ++ xs) sem ∈ prods) ->
      wp (ptPartial :: ptNondet :: ptParse :: Nil) (unfold fromProductions (buildParser {A} xs) n) (λ _ str' -> length str' ≤ length str) str
    nextBuildingStep : ∀ {A} str n -> Succ (length str * bound + bound) < n ->
      (xs : Symbols) ->
      wp (ptPartial :: ptNondet :: ptParse :: Nil) (unfold fromProductions (buildParser {A} xs) n) (λ _ str' -> length str' ≤ length str) str
    filterStep : ∀ A str n (cs : LeftRecChain prods A) -> Succ (length str * bound + bound ∸ chainLength cs) ≤ n ->
      wp (ptPartial :: ptNondet :: ptParse :: Nil) (unfold fromProductions (fromProductions A) n) (λ _ str' -> length str' ≤ length str) str
    filterStep' : ∀ prods' A str n (cs : LeftRecChain prods A) -> Succ (length str * bound + bound ∸ chainLength cs) ≤ n ->
      (∀ {x} -> x ∈ prods' -> x ∈ prods) ->
      wp (ptPartial :: ptNondet :: ptParse :: Nil) (unfold fromProductions (foldr (split (∈Tail ∈Head)) (fail (∈Tail ∈Head)) (map fromProduction (filterLHS A prods'))) n) (λ _ str' -> length str' ≤ length str) str

    unfold->>= : ∀ {a b I O es} (S : Free (ERec I O :: es) a) (f : a -> Free (ERec I O :: es) b) ->
      ∀ r n -> unfold r (S >>= f) n == (unfold r S n >>= λ x -> unfold r (f x) n)
    unfold->>= (Pure x) f r n = refl
    unfold->>= (Step ∈Head c k) f r Zero = cong (Step ∈Head Fail) (extensionality λ ())
    unfold->>= (Step ∈Head c k) f r (Succ n) = trans (cong (unfold r (r c) n >>=_) (extensionality λ x -> unfold->>= (k x) f r (Succ n))) (sym (>>=-assoc (unfold r (r c) n) _ _))
    unfold->>= (Step (∈Tail i) c k) f r n = cong (Step (∈Tail i) c) (extensionality λ x -> unfold->>= (k x) f r n)

    +-∸-≤ : ∀ a b c -> (c ≤ b) -> a ≤ b + a ∸ c
    +-∸-≤ Zero b c lt = z≤n
    +-∸-≤ (Succ a) b Zero lt = ≤-trans (s≤s (+-∸-≤ a b Zero lt)) (≤-reflexive (sym (+-suc b a)))
    +-∸-≤ (Succ a) (Succ b) (Succ c) (s≤s lt) = +-∸-≤ (Succ a) b c lt
    +-∸-< : ∀ a b c -> (c < b) -> a < b + a ∸ c
    +-∸-< Zero (Succ b) Zero (s≤s z≤n) = s≤s z≤n
    +-∸-< Zero (Succ (Succ b)) (Succ c) (s≤s (s≤s lt)) = ≤-trans (≤-reflexive (sym (m+n∸n≡m 1 b))) (∸-mono (≤-reflexive (cong Succ (sym (+-identityʳ b)))) lt)
    +-∸-< (Succ a) (Succ b) Zero (s≤s lt) = s≤s (+-mono-≤ (z≤n {b}) ≤-refl)
    +-∸-< (Succ a) (Succ b) (Succ c) (s≤s lt) = +-∸-< (Succ a) b c lt

    Succ-∸-Succ : ∀ a b -> Succ b ≤ a -> Succ (a ∸ (Succ b)) == a ∸ b
    Succ-∸-Succ (Succ a) Zero (s≤s z≤n) = refl
    Succ-∸-Succ (Succ (Succ a)) (Succ b) (s≤s (s≤s lt)) = Succ-∸-Succ (Succ a) b (s≤s lt)

    map-snoc : ∀ {a b} {f : a -> b} x xs ys -> map f xs ++ (f x :: ys) == map f (xs ++ (x :: Nil)) ++ ys
    map-snoc x Nil ys = refl
    map-snoc {f = f} x (x' :: xs) ys = cong (f x' ::_) (map-snoc x xs ys)

    subst2 : ∀ {A} {B : A -> Set} (C : (x : A) -> B x -> Set) {x x' : A} {y : B x} (p : x == x') -> C x y -> C x' (subst B p y)
    subst2 C refl z = z

    next-nonterminal : ∀ {A B Bs xs sem} -> prod A (map Inr Bs ++ (Inr B :: xs)) sem ∈ prods -> prod A (map Inr (Bs ++ (B :: Nil)) ++ xs) (subst (λ xs' -> ⟦ xs' ∥ A ⟧) (map-snoc B Bs xs) sem) ∈ prods
    next-nonterminal {A} {B} {Bs} {xs} {sem} i = subst2 (λ xs' sem' → prod A xs' sem' ∈ prods) (map-snoc B Bs xs) i

    wp-monotone : ∀ {a P Q} (S : Free _ a) t -> (∀ x t -> P x t -> Q x t) ->
      wp (ptPartial :: ptNondet :: ptParse :: Nil) S P t -> wp (ptPartial :: ptNondet :: ptParse :: Nil) S Q t
    wp-monotone (Pure x) t imp asm = imp x _ asm
    wp-monotone (Step ∈Head c k) t imp asm = asm
    wp-monotone (Step (∈Tail ∈Head) Fail k) t imp asm = asm
    wp-monotone (Step (∈Tail ∈Head) Split k) t imp (fst , snd) = wp-monotone (k True) t imp fst , wp-monotone (k False) t imp snd
    wp-monotone (Step (∈Tail (∈Tail ∈Head)) Parse k) Nil imp asm = asm
    wp-monotone (Step (∈Tail (∈Tail ∈Head)) Parse k) (x :: xs) imp asm = wp-monotone (k x) xs imp asm

    firstBuildingStep str (Succ n) cs (s≤s lt) Bs Nil i = ≤-refl
    firstBuildingStep {A} str (Succ n) cs (s≤s lt) Bs (Inr B :: xs) {sem} i = wpToBind _
      (unfold fromProductions (fromProductions B) n) _ str
      (wp-monotone
        (unfold fromProductions (fromProductions B) n) str
        (λ _ str' lt' -> subst (λ S -> wp _ S _ str') (sym (unfold->>= (buildParser xs) _ fromProductions (Succ n)))
        (wpToBind _ (unfold fromProductions (buildParser xs) (Succ n)) _ str'
          (wp-monotone (unfold fromProductions (buildParser xs) (Succ n)) str'
            (λ _ str'' lt'' → ≤-trans lt'' lt')
            (firstBuildingStep str' (Succ n) cs (s≤s (≤-trans (∸-mono (+-mono-≤ (*-mono-≤ lt' (≤-refl {bound})) (≤-refl {bound})) (≤-refl {chainLength cs})) lt)) (Bs ++ (B :: Nil)) xs (next-nonterminal i)))))
        (filterStep B str n (i :: cs) (≤-trans (≤-reflexive (Succ-∸-Succ (length str * bound + bound) (chainLength cs) (+-mono-≤ (z≤n {length str * bound}) (H cs)))) lt)))
    firstBuildingStep Nil (Succ n) cs (s≤s lt) Bs (Inl x :: xs) i = tt
    firstBuildingStep (s :: str) (Succ n) cs (s≤s lt) Bs (Inl x :: xs) i with x ≟t s
    ... | yes refl = wp-monotone (unfold fromProductions (buildParser xs) (Succ n)) str (λ x str' lt -> ≤-step lt)
      (nextBuildingStep str (Succ n)
        (s≤s (≤-trans (≤-trans (+-∸-< (length str * bound + bound) bound (chainLength cs) (H cs)) (≤-reflexive (cong (_∸ chainLength cs) (sym (+-assoc bound _ _))))) lt))
        xs)
    ... | no ¬p = tt

    nextBuildingStep str (Succ n) (s≤s lt) Nil = ≤-refl
    nextBuildingStep {A} str (Succ n) (s≤s lt) (Inr B :: xs) = wpToBind _
      (unfold fromProductions (fromProductions B) n) _ str
      (wp-monotone
        (unfold fromProductions (fromProductions B) n) str
        (λ _ str' lt' -> subst (λ S → wp _ S _ str') (sym (unfold->>= (buildParser xs) _ fromProductions (Succ n)))
        (wpToBind _ (unfold fromProductions (buildParser xs) (Succ n)) _ str'
          (wp-monotone (unfold fromProductions (buildParser xs) (Succ n)) str'
          (λ _ str'' lt'' -> ≤-trans lt'' lt')
          (nextBuildingStep str' (Succ n) (s≤s (≤-trans (s≤s (+-mono-≤ (*-mono-≤ lt' ≤-refl) (≤-refl {bound}))) lt)) xs))))
      (filterStep B str n Nil lt))
    nextBuildingStep Nil (Succ n) (s≤s lt) (Inl x :: xs) = tt
    nextBuildingStep (s :: str) (Succ n) (s≤s lt) (Inl x :: xs) with x ≟t s
    ... | yes refl = wp-monotone (unfold fromProductions (buildParser xs) (Succ n)) str (λ x str' lt -> ≤-step lt) (nextBuildingStep str (Succ n) (s≤s (≤-trans (s≤s (+-mono-≤ (+-mono-≤ (z≤n {bound}) ≤-refl) (≤-refl {bound}))) lt)) xs)
    ... | no ¬p = tt

    filterStep A str n cs lt = filterStep' prods A str n cs lt (λ i -> i)
    filterStep' Nil A str n cs lt i = tt
    filterStep' (prod lhs rhs sem :: prods') A str n cs lt subset with A ≟n lhs
    ... | yes refl =
      subst (λ S -> wp _ S _ _) (sym (unfold->>= (buildParser rhs) (λ f -> Pure (f sem)) fromProductions n))
      (wpToBind _ (unfold fromProductions (buildParser rhs) n) _ str (wp-monotone
        (unfold fromProductions (buildParser rhs) n) _
        (λ _ str' lt' -> lt')
        (firstBuildingStep str n cs lt Nil rhs (subset ∈Head)))) ,
      filterStep' prods' A str n cs lt λ i -> subset (∈Tail i)
    ... | no ¬p =
      filterStep' prods' A str n cs lt λ i -> subset (∈Tail i)
\end{code}

\section{Left factorisation?}
In that proof, do we need to left factorise the language? In that case, can we say something about that operation?
\end{document}


\documentclass{llncs}

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

  ptNondet : (c : CNondet) -> (RNondet c -> Set) -> Set
  ptNondet Fail P = ⊤
  ptNondet Split P = P True ∧ P False

  wpNondetAll : {a : Set} -> Free ENondet a ->
    (a -> Set) -> Set
  wpNondetAll S P = wpFree ptNondet S P
\end{code}
%if style == newcode
\begin{code}
ptNondet = NoCombination.ptNondet
\end{code}
%endif

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
\end{code}
%if style == newcode
\begin{code}
module AlmostRegex where
  open NoCombination
\end{code}
%endif
\begin{code}
  allSplits : ∀ {a} -> (xs : List a) -> Free ENondet (SplitList xs)
  allSplits Nil = Pure (splitList Nil Nil refl)
  allSplits (x :: xs) = split
    (Pure (splitList Nil (x :: xs) refl))
    (allSplits xs >>= λ spl -> Pure (splitList (x :: SplitList.lhs spl) (SplitList.rhs spl) (cong (Cons x) (SplitList.cat spl))))
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
\begin{code}
module Combinations where
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
    (allSplits i xs >>= λ spl -> Pure (splitList (x :: SplitList.lhs spl) (SplitList.rhs spl) (cong (Cons x) (SplitList.cat spl))))

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
without having to use |wpBind| in between.
Unfortunately, we still need |wpBind| to deal with the call to |allSplits|.
We give a proof specialized for |wpMatch|,
although it generalizes to all |pts| passed to |wpFree|.
\begin{code}
  wpBind : ∀ {a b} post (mx : Free _ a) (f : a -> Free _ b) ->
    wpMatch mx post ->
    ∀ P -> (∀ x -> post x -> wpMatch (f x) P) ->
    wpMatch (mx >>= f) P
  wpBind post (Pure x) f mxH P postH = postH x mxH
  wpBind post (Step ∈Head (r , xs) k) f mxH P postH = λ o H -> wpBind post (k o) f (mxH o H) P postH
  wpBind post (Step (∈Tail ∈Head) Fail k) f mxH P postH = mxH
  wpBind post (Step (∈Tail ∈Head) Split k) f (fst , snd) P postH =
    wpBind post (k True) f fst P postH , wpBind post (k False) f snd P postH
\end{code}

We can reuse exactly the same proof to show |allSplits| is correct,
since we use the same semantics for the effects in |allSplits|.
%if style == newcode
\begin{code}
  allSplitsCorrect : ∀ (xs : String) ->
    wpMatch (allSplits (∈Tail ∈Head) xs) (λ _ -> ⊤)
  allSplitsCorrect Nil = tt
  allSplitsCorrect (x :: xs) = tt , wpBind (const ⊤) (allSplits _ xs) _ (allSplitsCorrect xs) _ λ _ _ -> tt
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
  pf ((l · r) , xs) P (preH , postH) = wpBind _ (allSplits (∈Tail ∈Head) xs) _ (allSplitsCorrect xs) P
    λ {(splitList lhs rhs refl) _ mls lH mrs rH -> postH _ (Concat lH rH)}
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
  ... | no ¬p = no λ { (m , Mark x) → ¬p (_ , x) }

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

Since |dmatch| always consumes a character before going in recursion, we can easily prove it calls itself on smaller arguments.
This means that for all input values, after substituting itself in the definition enough times, we get rid of all (general) recursion.
In other words: |dmatch| terminates.
\begin{code}
  terminates-in : ∀ {I O a es} (pts : PTs es) (f : (i : I) -> Free (ERec I O :: es) (O i)) ->
    Free (ERec I O :: es) a -> Nat -> Set
  terminates-in pts f S Zero = ⊥
  terminates-in pts f (Pure x) (Succ n) = ⊤
  terminates-in pts f (Step ∈Head c k) (Succ n) = terminates-in pts f (f c) n ∧ ∀ x -> terminates-in pts f (k x) (Succ n)
  terminates-in pts f (Step (∈Tail i) c k) (Succ n) = lookupPT pts i c λ x -> terminates-in pts f (k x) (Succ n)
  termination : ∀ {I O es} (pts : PTs es) (f : (i : I) -> Free (ERec I O :: es) (O i)) -> Set
  termination pts f = ∀ i -> Sigma Nat λ n -> terminates-in pts f (f i) n

  dmatch-terminates : termination (ptNondet :: Nil) (dmatch ∈Head (∈Tail ∈Head))
  dmatch-terminates (r , xs) = Succ (length xs) , lemma r xs
    where
    lemma : ∀ r xs -> terminates-in (ptNondet :: Nil) (dmatch ∈Head (∈Tail ∈Head)) (dmatch ∈Head (∈Tail ∈Head) (r , xs)) (Succ (length xs))
    lemma r Nil with ε? r
    lemma r Nil | yes p = tt
    lemma r Nil | no ¬p = tt
    lemma r@Empty (x :: xs) = lemma (d r /d x) xs , λ _ -> tt
    lemma r@Epsilon (x :: xs) = lemma (d r /d x) xs , λ _ -> tt
    lemma r@(Singleton _) (x :: xs) = lemma (d r /d x) xs , λ _ -> tt
    lemma r@(_ · _) (x :: xs) = lemma (d r /d x) xs , λ _ -> tt
    lemma r@(_ ∣ _) (x :: xs) = lemma (d r /d x) xs , λ _ -> tt
    lemma r@(_ *) (x :: xs) = lemma (d r /d x) xs , λ _ -> tt
    lemma r@(Mark n _) (x :: xs) = lemma (d r /d x) xs , (λ _ -> tt)
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
  consequence : ∀ {a b} (S : Free _ a) (f : a -> Free _ b) P ->
    wpMatch (S >>= f) P -> wpMatch S (λ x -> wpMatch (f x) P)
  consequence (Pure x) f P H = H
  consequence (Step ∈Head c k) f P H o x = consequence (k o) f P (H o x)
  consequence (Step (∈Tail ∈Head) Fail k) f P .tt = tt
  consequence (Step (∈Tail ∈Head) Split k) f P (fst , snd) = consequence (k True) f P fst , consequence (k False) f P snd
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
  refinement (l ∣ r) (x :: xs) P (fst , snd) = λ { o (OrLeft H) → fst o (derivativeCorrect _ _ _ _ H) ; o (OrRight H) → snd o (derivativeCorrect _ _ _ _ H)}
  refinement (r *) Nil P H = H
  refinement (r *) (x :: xs) P H = λ {ms (Concat ml mr) → H _ (Concat (derivativeCorrect _ _ _ _ ml) mr)}
  refinement (Mark n r) Nil P H with ε? r
  ... | yes (fst , snd) = H _ snd
  ... | no ¬p = tt
  refinement (Mark n r) (x :: xs) P H = λ {o (Mark m) → H _ (derivativeCorrect r _ _ _ m)}
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
      d_/d_ : (j : Size< i) -> Terminal -> Trie j a
\end{code}

Our last viewpoint of grammar is a much more computational one: the list-of-succesful-parses type.
\begin{code}
  Parser = ∀ {a} -> List Terminal -> List a
\end{code}

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


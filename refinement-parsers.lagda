\documentclass{article}

\title{Verified parsers using the refinement calculus and algebraic effects}
\author{Tim Baanen \and Wouter Swierstra}

\begin{document}
There are various ways to write a parser in functional languages, for example using parser combinations.
How do we ensure these parsers are correct?
Previous work has shown that predicate transformers are useful for verification of programs using algebraic effects.
This paper will show how predicate transformers and algebraic effects allow for formal verification of parsers.

\section{Recap: algebraic effects and predicate transformers}
Algebraic effects were introduced to allow for incorporating side effects in functional languages.
For example, nondeterministic programs:
\begin{code}
ENondet = eff CNondet RNondet
\end{code}

To give specifications of programs that incorporate effects,
we can use predicate transformers.
\begin{code}
wpNondetAll : (a \to Free ENondet b) \to (a \to b \to Set) \to a \to Set
wpNondetAll = ?
\end{code}

\section{Almost parsing regular languages}
As an example of using nondeterminism,
we can define the type of regular expressions |Regex| in Agda,
and a relation |Match| on |Regex| and |String|.

Using nondeterminism as an effect, we create a function that takes a |Regex| and |String| and gives all potential matchings.
Unfortunately, we get stuck in the case of _*, since it is not immediately obvious that this terminates.
We just fail in this case.
\begin{code}
match : (r,xs : Pair Regex String) \to Free ENondet (Match r,xs)
match = ?
\end{code}

Still, we can prove that this program works, as long as the regex does not contain |_*|.
Since the type guarantees that all output is a correct match,
we only need to ensure that there is output as long as a correct match exists.
Thus, the precondition states the absence of the Kleene star and that there is some way to match,
and the postcondition does not give any restrictions on the output.
\begin{code}
pre : (r,xs : Pair Regex String) \to Set
pre (r , xs) = Par (hasNo* r) (\exists Match (r , xs))
post : (r,xs : Pair Regex String) \to Match (r,xs) \to Set
post _ _ = \top 

pf : wpSpec [[ pre , post ]] \refined wpNondetAll match
pf = ?
\end{code}

\section{Combining nondeterminism and general recursion}
In order to give a regex parser that also supports the Kleene star,
we add another effect: general recursion.

Here is the corresponding predicate transformer:


The original |Free| monad is modified to support a list of effects instead of a single one,
which corresponds to taking the coproduct of the functors that |Free| is a free monad over.

Now we need give new definitions of |wp|, |wpNondet| and |wpRec|.
\begin{code}
wp : \forall {a b} \to (a \to Free [] b) \to (a \to b \to Set) \to (a \to Set)
wpNondet : \forall {a b} \to (i : ENondet \in es) \to (a \to Free es b) \to (a \to Free (delete es i) b \to Set) \to (a \to Set) -- (or make the smart constructors take (ENondet \in es) and the predicate transformers take Free (ENondet :: es) b to Free es b)?
\end{code}

\section{Recursively parsing every regular expression}

Now we are able to handle the Kleene star:

We can also show correctness in the case of |_*|.

However, in this proof we do not show termination of the parsing, so it is just a proof of partial correctness.
To prove termination, it is easier to write a new parser that refines the previous implementation.

\section{Termination, using derivatives}
We can use the Brzozowski derivative to advance the regular expression a single character, giving the function |dmatch|.

Since |dmatch| always consumes a character before going in recursion, we can easily prove it calls itself on smaller arguments.
This means that for all input values, after substituting itself in the definition enough times, we get rid of all (general) recursion.
In other words: |dmatch| terminates.

Moreover, |dmatch| is a refinement of |match|, which means it is also correct:

\section{Different viewpoints of grammars}
In classical logic, a language is no more than a set of strings, or a predicate over strings: |String \to Set|.
Constructively, such predicates (even when decidable) are not very useful: the language $\{xs | xs is a valid proof of the Riemann Hypothesis\}$ has no defined cardinality.
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
Consider the language given by E \to 'a' E | 'b'.
However, we can show that substituting a fixed number of times, and then giving up using |fail|.
If each right hand side has a nonterminal, then the parser terminates in this weaker sense.

\section{Left factorisation?}
In that proof, do we need to left factorise the language? In that case, can we say something about that operation?
\end{document}

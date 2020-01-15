# A predicate transformer semantics of parsing

This repository contains the full source code for the paper "A predicate transformer semantics of parsing",
including lemmas we have omitted from the print version for sake of readability.

The main source file is `refinement-parsers.lagda`; `lhs2TeX` is used to extract the Agda code for verification and the LaTeX code for compiling the paper.
The imported file `Prelude.agda` contains basic definitions.
The `.fmt` files contain formatting information to instruct `lhs2Tex` how to render various operators.
The remaining files are used by LaTeX for style information.

## Instructions

To check the proofs, you need Agda (tested with version 2.6.0.1) including its standard library, and `lhs2TeX` (tested with version 1.22).
If you have `make`, simply run `make check`; otherwise run `lhs2TeX --newcode --no-pragmas refinement-parsers.lagda -o Check.agda` to extract the Agda code so that running `agda Check.agda` will check it.

To compile the paper to a PDF, you need `lhs2TeX` (tested with version 1.22), XeLaTeX (tested with version 3.14159265-2.6-0.999991) and `biber` (tested with version 2.13).
If you have `make` and `latexmk`, simply run `make`; otherwise run `lhs2TeX --agda --poly -o refinement-parsers.tex refinement-parsers.lagda` to extract the LaTeX code and compile it as appropriate for your TeX installation.

## Context-free grammars
In additions to the regular expression parser described in the paper,
we developed a verified parser for context-free grammars.
A description of the development, including code, will be included as an appendix to the paper
by uncommenting the line `\def\includeCFGs{}` in the preamble of `refinement-parsers.lagda` and re-running the compilation.
The code for the context-free parser is automatically included with the extracted Agda code in `Check.agda`.

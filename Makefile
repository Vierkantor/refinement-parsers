default : refinement-parsers.pdf

%.tex : %.lagda preamble.tex
	lhs2TeX --agda --poly -o $@ $<

%.pdf : %.tex
	latexmk -xelatex $<

clean :
	rm -f *.aux *.log *.out *.ptb *.bbl *.blg *.agdai *.fls Check.agda refinement-parsers.tex refinement-parsers.pdf

check :
	lhs2TeX --newcode  --no-pragmas refinement-parsers.lagda -o Check.agda
#	cp src/Prelude.agda .
	agda Check.agda
#	rm -rf Check.agda*
	echo 'Check succeeded'

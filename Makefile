default : refinement-parsers.pdf

%.tex : %.lagda preamble.tex %.fmt
	lhs2TeX --agda --poly -o $@ $<

%.pdf : %.tex
	latexmk -xelatex $<

clean :
	rm -f *.aux *.log *.out *.ptb *.bbl *.blg *.agdai *.fls Check.agda refinement-parsers.tex refinement-parsers.pdf

check :
	lhs2TeX --newcode  --no-pragmas refinement-parsers.lagda -o Check.agda
	agda Check.agda
	echo 'Check succeeded'

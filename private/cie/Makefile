TEXFILES = cie.tex \
	macros.tex \
	introduction.tex \
	modest_sets.tex \
	specifications.tex \
	logic.tex \
	implementation.tex \
	examples.tex \
	comparison.tex \
	wtype.tex

all: cie.pdf cie.ps

cie.ps: $(TEXFILES) rzbib.bib
	latex cie.tex
	bibtex cie
	latex cie.tex
	latex cie.tex
	dvips cie.dvi -o cie.ps

cie.pdf: cie.ps
	pdflatex cie.tex

clean:
	/bin/rm -f *.{aux,log} cie.{ps,pdf,bbl,blg,pdfsync}
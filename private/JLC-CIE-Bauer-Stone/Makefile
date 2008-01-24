# See README.txt for details.

TEXFILES = macros.tex \
	introduction.tex \
	modest_sets.tex \
	specifications.tex \
	logic.tex \
	implementation.tex \
	examples.tex \
	comparison.tex \
	wtype.tex

default: paper.pdf

all: paper.pdf

paper.pdf: paper.tex $(TEXFILES) rzbib.bib wtype.mli
	pdflatex paper.tex
	bibtex paper
	pdflatex paper.tex
	pdflatex paper.tex

clean:
	/bin/rm -f paper.aux
	/bin/rm -f paper.{aux,ps,pdf,bbl,blg,pdfsync,dvi}

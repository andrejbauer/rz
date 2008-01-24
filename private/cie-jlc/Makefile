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

default: main.pdf

all: cie-long.pdf cie-short.pdf

main.pdf: main.tex $(TEXFILES) rzbib.bib wtype.mli
	latex main.tex
	bibtex main
	latex main.tex
	pdflatex main.tex

cie-long.pdf: cie-long.tex $(TEXFILES) rzbib.bib wtype.mli
	latex cie-long.tex
	bibtex cie-long
	latex cie-long.tex
	pdflatex cie-long.tex

cie-short.pdf: cie-short.tex $(TEXFILES) rzbib.bib wtype.mli
	latex cie-short.tex
	bibtex cie-short
	latex cie-short.tex
	pdflatex cie-short.tex

clean:
	/bin/rm -f *.{aux,log} cie-{long,short}.{ps,pdf,bbl,blg,pdfsync,dvi} main.{ps,pdf,bbl,blg,pdfsync,dvi}
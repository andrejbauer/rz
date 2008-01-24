1. CONTACT

If you have any questions or problems with these files, please contact
me at Andrej.Bauer@andrej.com.


2. HOW TO GENERATE THE PDF VERSION OF THE PAPER

To generate a PDF file run the command

  make

on a Unix system. Under windows, run 

  pdflatex paper.tex
  bibtex paper
  pdflatex paper.tex
  pdflatex paper.tex


3. THE STRUCTURE OF LATEX FILES

We strove to use standard LaTeX.

The main LaTeX file is paper.tex.

There are a number of source code files (*.thy and *.mli) which are
included into tha LaTeX files. We use the fancyvrb package to display
source code. Depending on the format of the journal, it may be hard to
fit long lines of source code onto the page, in which case please
contact me to find a solution. (Please do not break the lines of
source code by yourself, you could change the meaning.)

Right at the top of paper.tex there is a switch which selects between
the long and the short version of the paper. Please do not touch this,
i.e., the long version is the that was submitted for publication in
the journal. The short version was published in the conference
proceedings.


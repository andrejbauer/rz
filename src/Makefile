# Configure the name of the executable

# Linux, Unix, MacOS
EXECUTABLE=rz

# Windows
#EXECUTABLE=rz.exe

# Probably you do not have to change anything below this line

SOURCES = \
	flags.ml \
	name.ml \
	syntax.ml \
	message.ml \
	parser.ml \
	lexer.ml \
	logic.ml \
	error.ml \
	logicrules.ml \
        infer.ml \
        outsyn.ml \
	pp.ml \
	rename.ml \
	outsynrules.ml \
	coqpp.ml \
	thin.ml \
        opt.ml \
        translate.ml \
	rz.ml

OCAMLC = ocamlc
OCAMLCP = ocamlcp
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
OCAMLYFLAGS = -v

INCLUDES =

OCAMLFLAGS = $(INCLUDES) -g # -p a
OCAMLCPFLAGS = 
OCAMLOPTFLAGS =  $(INCLUDES)

CMO = $(SOURCES:.ml=.cmo)
CMX = $(SOURCES:.ml=.cmx)

LIBS = str.cma
LIBSOPT = str.cmxa

TARGET = $(EXECUTABLE)
TARGETOPT = opt_$(EXECUTABLE)

default: $(TARGET) 

all: $(TARGET) $(TARGETOPT)
	echo $(TARGET)
	echo $(TARGETOPT)

test: $(TARGET)
	cd tests && ./test.sh

vtest: $(TARGET)
	cd tests && ./test.sh -v

parser.cmo: parser.ml parser.cmi

parser.cmx: parser.ml parser.cmi

parser.cmi: parser.mli 
	$(OCAMLC) $(OCAMLFLAGS) -c parser.mli

lexer.ml: lexer.mll 
	$(OCAMLLEX) lexer.mll

parser.ml parser.mli: parser.mly
	$(OCAMLYACC) $(OCAMLYFLAGS) parser.mly

$(TARGET): %: $(CMO)
	$(OCAMLC) -o $(TARGET) $(OCAMLFLAGS) $(LIBS) $+ 

$(TARGETOPT): %: $(CMX)
	$(OCAMLOPT) -o $(TARGETOPT) $(OCAMLOPTFLAGS) $(LIBSOPT) $+

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

%.ml: %.mll
	$(OCAMLLEX) $<

%.ml %.mli: %.mly
	$(OCAMLYACC) $(OCAMLYFLAGS) $<

# Clean.
clean:
	rm -f $(TARGET) $(TARGETOPT) *.cm[iox] *.o *~ *.dvi *.ps *.log *.aux
	rm -f parser.ml
	rm -f lexer.ml
	rm -f parser.mli
	cd tests && make clean

# Depend.
depend: clean
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

.PHONY: clean depend

include .depend

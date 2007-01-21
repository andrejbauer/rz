# Configure the name of the executable

# Linux, Unix, MacOS
EXECUTABLE=rz

# Windows
#EXECUTABLE=rz.exe

# Probably you do not have to change anything below this line

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

BYTE_OBJS = name.cmo \
	syntax.cmo \
	message.cmo \
	parser.cmo \
	lexer.cmo \
	flags.cmo \
	logic.cmo \
	error.cmo \
	logicrules.cmo \
        infer.cmo \
        outsyn.cmo \
	outsynrules.cmo \
	rename.cmo \
	pp.cmo \
	thin.cmo \
        opt.cmo \
        translate.cmo

LIB_OBJS = unix.cma str.cma

TARGETS = rz

default: $(TARGETS) 

all: $(TARGETS)
	echo $(TARGETS)

test: $(TARGETS)
	cd tests && ./test.sh

vtest: $(TARGETS)
	cd tests && ./test.sh -v

parser.cmo: parser.ml parser.cmi

parser.cmx: parser.ml parser.cmi

parser.cmi: parser.mli 
	$(OCAMLC) $(OCAMLFLAGS) -c parser.mli

lexer.ml: lexer.mll 
	$(OCAMLLEX) lexer.mll

parser.ml parser.mli: parser.mly
	$(OCAMLYACC) $(OCAMLYFLAGS) parser.mly

$(TARGET): %: $(BYTE_OBJS) %.cmo
	$(OCAMLC) -o $(EXECUTABLE) $(OCAMLFLAGS) $(LIB_OBJS) $+ 

# Suffixes.
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
	rm -f $(EXECUTABLE) *.cm[iox] *.o *~ *.dvi *.ps *.log *.aux
	rm -f parser.ml
	rm -f lexer.ml
	rm -f parser.mli
	cd tests && make clean

# Depend.
depend: clean
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

.PHONY: clean depend

include .depend

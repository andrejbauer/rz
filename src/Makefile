OCAMLC = ocamlc
OCAMLCP = ocamlcp
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
OCAMLYFLAGS = -v
TAR = tar
ZIP = zip

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

OPT_OBJS = $(subst .cmo,.cmx,$(BYTE_OBJS))

LIB_OBJS = unix.cma str.cma

LIB_OPT_OBJS = $(subst .cma,.cmxa,$(subst .cmo,.cmx,$(LIB_OBJS)))

TARGETS = rz

OPT_TARGETS = $(addsuffix .opt,$(TARGETS))

default: $(TARGETS) 

all: $(TARGETS) $(OPT_TARGETS)
	echo $(OPT_TARGETS); echo $(TARGETS)

test: $(TARGETS)
	cd tests && ./test.sh

vtest: $(TARGETS)
	cd tests && ./test.sh -v

#parser.cmo: parser.ml parser.cmi
#
#parser.cmi: parser.mli syntax.cmi
#	$(OCAMLC) $(OCAMLFLAGS) -c parser.mli
#
#lexer.cmi: lexer.mli parser.mli syntax.mli
#	$(OCAMLC) $(OCAMLFLAGS) -c lexer.mli

parser.cmo: parser.ml parser.cmi

parser.cmx: parser.ml parser.cmi

parser.cmi: parser.mli 
	$(OCAMLC) $(OCAMLFLAGS) -c parser.mli

lexer.ml: lexer.mll 
	$(OCAMLLEX) lexer.mll

parser.ml parser.mli: parser.mly
	$(OCAMLYACC) $(OCAMLYFLAGS) parser.mly

$(TARGETS): %: $(BYTE_OBJS) %.cmo
	$(OCAMLC) -o rz $(OCAMLFLAGS) $(LIB_OBJS) $+ 

$(OPT_TARGETS): %.opt: $(OPT_OBJS) %.cmx 
	$(OCAMLOPT) -o rz.opt $(OCAMLOPTFLAGS) $(LIB_OPT_OBJS) $+

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
	rm -f $(TARGETS) $(OPT_TARGETS) *.cm[iox] *.o *~ *.dvi *.ps *.log *.aux
	rm -f parser.ml
	rm -f lexer.ml
	rm -f parser.mli
	cd tests; make clean

# Depend.
depend: clean
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

.PHONY: clean depend

include .depend

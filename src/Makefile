OCAMLC = ocamlc
OCAMLCP = ocamlcp
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
OCAMLYFLAGS = -v

INCLUDES =

OCAMLFLAGS = $(INCLUDES) -g
OCAMLCPFLAGS = 
OCAMLOPTFLAGS =  $(INCLUDES) -unsafe -inline 5 

BYTE_OBJS = name.cmo \
	syntax.cmo \
	message.cmo \
	coq_parser.cmo \
	coq_lexer.cmo \
	flags.cmo \
	logic.cmo \
	error.cmo \
	logicrules.cmo \
        newinfer.cmo \
        outsyn.cmo \
	pp.cmo \
        opt.cmo \
        translate.cmo

OPT_OBJS = $(subst .cmo,.cmx,$(BYTE_OBJS))

LIB_OBJS = unix.cma str.cma

LIB_OPT_OBJS = $(subst .cma,.cmxa,$(subst .cmo,.cmx,$(LIB_OBJS)))

TARGETS = rz

OPT_TARGETS = $(addsuffix .opt,$(TARGETS))

default: $(TARGETS) rzinfer

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

coq_parser.cmo: coq_parser.ml coq_parser.cmi

coq_parser.cmi: coq_parser.mli syntax.cmo name.cmo
	$(OCAMLC) $(OCAMLFLAGS) -c coq_parser.mli

coq_lexer.ml: coq_lexer.mll syntax.cmo name.cmo
	$(OCAMLLEX) coq_lexer.mll

$(TARGETS): %: $(BYTE_OBJS) %.cmo
	$(OCAMLC) -o rz $(OCAMLFLAGS) $(LIB_OBJS) $+ 

$(OPT_TARGETS): %.opt: $(OPT_OBJS) %.cmx 
	$(OCAMLOPT) -o rz.opt $(OCAMLOPTFLAGS) $(LIB_OPT_OBJS) $+

rzinfer: name.cmo \
	syntax.cmo \
	message.cmo \
	coq_parser.cmo \
	coq_lexer.cmo \
	flags.cmo \
	logic.cmo \
	error.cmo \
	possibility.cmo \
	logicrules.cmo \
        newinfer.cmo \
	rzinfer.cmo	
	$(OCAMLC) -o rzinfer $(OCAMLFLAGS) $(LIB_OBJS) $+ 

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

# Depend.
depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

.PHONY: clean depend

include .depend

OCAMLC = ocamlc
OCAMLCP = ocamlcp
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
OCAMLYFLAGS = -v

INCLUDES =

OCAMLFLAGS = -w p $(INCLUDES) -g
OCAMLCPFLAGS = 
OCAMLOPTFLAGS = -w p $(INCLUDES) -unsafe -inline 5 

BYTE_OBJS = syntax.cmo \
	message.cmo \
	parser.cmo \
	lexer.cmo \
	context.cmo \
        infer.cmo \
	logic.cmo \
        outsyn.cmo \
        opt.cmo \
        translate.cmo \

OPT_OBJS = $(subst .cmo,.cmx,$(BYTE_OBJS))

LIB_OBJS = unix.cma

LIB_OPT_OBJS = $(subst .cma,.cmxa,$(subst .cmo,.cmx,$(LIB_OBJS)))

TARGETS = rz

OPT_TARGETS = $(addsuffix .opt,$(TARGETS))

default: $(TARGETS)

all: $(TARGETS) $(OPT_TARGETS)
	echo $(OPT_TARGETS); echo $(TARGETS)

parser.cmo: parser.ml parser.cmi

parser.cmi: parser.mli syntax.cmi
	$(OCAMLC) $(OCAMLFLAGS) -c parser.mli

lexer.cmi: lexer.mli parser.mli
	$(OCAMLC) $(OCAMLFLAGS) -c lexer.mli

$(TARGETS): %: $(BYTE_OBJS) %.cmo
	$(OCAMLC) -o rz $(OCAMLFLAGS) $(LIB_OBJS) $+ 

$(OPT_TARGETS): %.opt: $(OPT_OBJS) %.cmx 
	$(OCAMLOPT) -o toplevel.opt $(OCAMLOPTFLAGS) $(LIB_OPT_OBJS) $+

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

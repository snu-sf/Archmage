OCAMLC=ocamlc -dtypes -g
OCAMLOPT=ocamlopt -dtypes -g
OCAMLDEP=ocamldep
SRCML= ptset ptmap dominator dominance ExternSSAgen gvnExtern
SRCMLI= ptset ptmap dominator dominance 
LIB=
INCLUDE=-I ../../_build/extraction -I ../../_build/lib

#setenv OCAMLRUNPARAM b

all: byte

byte:$(SRCML:=.cmo)

depend: $(SRCMLI:=.mli) $(SRCML:=.ml)
	@echo "  [ocamldep    ] "$(SRCMLI:=.mli) $(SRCML:=.ml) main.ml" > .depend"
	@$(OCAMLDEP) $(SRCMLI:=.mli) $(SRCML:=.ml) main.ml > .depend

.SUFFIXES: .ml .mli .cmo .cmi .cmx 

.ml.cmo:
	@echo "  [ocamlc    -c] "$<
	@$(OCAMLC) -dtypes $(INCLUDE) -c $<

.ml.cmx:
	@echo "  [ocamlopt  -c] "$<
	@$(OCAMLOPT) $(INCLUDE) -c $<

.mli.cmi:
	@echo "  [ocamlc    -c] "$<
	@$(OCAMLC) -dtypes $(INCLUDE) -c $<

clean : 
	\rm -f *.cmo *.cmi *.annot  *~ *.cmx *.opt *.byte *.o 

-include .depend




DY_HOME ?= ../../..

EXAMPLE_DIRS = ../request_response ..
include $(DY_HOME)/Makefile

test:
	cd $(DY_HOME)/obj; OCAMLPATH=$(FSTAR_HOME)/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_Example_RequestResponse_Debug.native
	$(DY_HOME)/obj/DY_Example_RequestResponse_Debug.native
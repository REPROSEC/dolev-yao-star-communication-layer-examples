DY_HOME ?= ../../..

EXAMPLE_DIRS = ../request_response_authenticated ..
include $(DY_HOME)/Makefile

test:
	cd $(DY_HOME)/obj; OCAMLPATH=$(FSTAR_HOME)/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_Example_RequestResponseAuthenticated_Debug.native
	$(DY_HOME)/obj/DY_Example_RequestResponseAuthenticated_Debug.native
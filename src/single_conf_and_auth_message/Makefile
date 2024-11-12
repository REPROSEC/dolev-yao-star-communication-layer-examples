DY_HOME ?= ../../..

EXAMPLES = single_conf_and_auth_message
EXAMPLE_DIRS = $(addprefix src/, $(EXAMPLES))
include $(DY_HOME)/Makefile

test:
	cd $(DY_HOME)/obj; OCAMLPATH=$(FSTAR_HOME)/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_Example_SingleConfAuthMessage_Debug.native
	$(DY_HOME)/obj/DY_Example_SingleConfAuthMessage_Debug.native
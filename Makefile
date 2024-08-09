DY_HOME ?= ../../..

EXAMPLES = single_conf_message single_auth_message
EXAMPLE_DIRS = $(addprefix src/, $(EXAMPLES))
include $(DY_HOME)/Makefile
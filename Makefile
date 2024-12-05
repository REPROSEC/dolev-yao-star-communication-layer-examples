DY_HOME ?= ../dolev-yao-star-extrinsic

EXAMPLES = single_conf_message single_auth_message single_conf_and_auth_message request_response
EXAMPLE_DIRS = $(addprefix src/, $(EXAMPLES))
include $(DY_HOME)/Makefile
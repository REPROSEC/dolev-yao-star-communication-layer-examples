DY_HOME ?= ../dolev-yao-star-extrinsic

EXAMPLES = src/single_conf_message src/single_auth_message src/single_conf_and_auth_message src/request_response src
EXAMPLE_DIRS = $(EXAMPLES)
include $(DY_HOME)/Makefile
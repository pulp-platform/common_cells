# SPDX-License-Identifier: Apache-2.0

VERILATOR ?= verilator

all: cc_ecc_encode cc_ecc_decode

cc_ecc_%: test/ecc/ecc_%.cpp test/ecc/ecc.cpp src/cc_pkg.sv src/cc_ecc_%.sv
	$(VERILATOR) --cc $^ --top-module $@ --trace --exe
	cd obj_dir && make -f V$@.mk > /dev/zero

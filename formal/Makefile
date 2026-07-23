# Copyright 2019 ETH Zurich and University of Bologna.
#
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License. You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.

# Authors:
# - Robert Balas <balasr@iis.ee.ethz.ch>
# - Philippe Sauter <phsauter@iis.ee.ethz.ch>
#
# Description: Formal Verification Targets
# Dispatch SymbiYosys proof runs for common_cells formal properties, including
# reset-controller half and composed CDC clear-sequencing checks.

YOSYS	?= yosys
SBY	?= sby
BENDER	?= bender
RM	?= rm -rf

FORMAL_BUILDDIR ?= build
FORMAL_FLIST := $(FORMAL_BUILDDIR)/cdc_reset_ctrlr.flist

all: fifo.check counter.check fall_through_register.check lzc.check \
	cdc_reset_ctrlr_half.check cdc_reset_ctrlr_composed.check heaviside.check

$(FORMAL_BUILDDIR):
	mkdir -p $@

$(FORMAL_FLIST): ../Bender.yml ../Bender.lock cc_cdc_reset_ctrlr_half_properties.sv \
		cc_cdc_reset_ctrlr_properties.sv | $(FORMAL_BUILDDIR)
	cd .. && $(BENDER) checkout
	cd .. && $(BENDER) script flist-plus -t formal > formal/$@

fifo.check: fifo.sby ../src/cc_fifo.sv cc_fifo_properties.sv
	$(SBY) -f $<
	touch $@

# delta_counter.check: delta_counter.sby ../src/cc_delta_counter.sv cc_delta_counter_properties.sv
#	$(SBY) -f $<
#	touch $@

counter.check: counter.sby ../src/cc_counter.sv ../src/cc_delta_counter.sv cc_counter_properties.sv
	$(SBY) -f $<
	touch $@

fall_through_register.check: fall_through_register.sby ../src/cc_fall_through_register.sv \
				../src/cc_fifo.sv
	$(SBY) -f $<
	touch $@

lzc.check: $(FORMAL_BUILDDIR)/lzc.check

$(FORMAL_BUILDDIR)/lzc.check: lzc.sby ../src/cc_pkg.sv ../src/cc_lzc.sv \
				cc_lzc_properties.sv cc_lzc_formal.sv | $(FORMAL_BUILDDIR)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/lzc $<
	touch $@

cdc_reset_ctrlr_half.check: $(FORMAL_BUILDDIR)/cdc_reset_ctrlr_half.check

$(FORMAL_BUILDDIR)/cdc_reset_ctrlr_half.check: cdc_reset_ctrlr_half.sby $(FORMAL_FLIST) | \
				$(FORMAL_BUILDDIR)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/cdc_reset_ctrlr_half $<
	touch $@

cdc_reset_ctrlr_composed.check: $(FORMAL_BUILDDIR)/cdc_reset_ctrlr_composed.check

$(FORMAL_BUILDDIR)/cdc_reset_ctrlr_composed.check: cdc_reset_ctrlr_composed.sby $(FORMAL_FLIST) | \
				$(FORMAL_BUILDDIR)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/cdc_reset_ctrlr_composed $<
	touch $@

heaviside.check: $(FORMAL_BUILDDIR)/heaviside.check

$(FORMAL_BUILDDIR)/heaviside.check: heaviside.sby ../src/cc_pkg.sv ../src/cc_heaviside.sv \
				cc_heaviside_properties.sv cc_heaviside_formal.sv | $(FORMAL_BUILDDIR)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/heaviside $<
	touch $@

.PHONY: all clean fifo.check counter.check fall_through_register.check lzc.check cdc_reset_ctrlr_half.check \
	cdc_reset_ctrlr_composed.check heaviside.check
clean:
	$(RM) $(FORMAL_BUILDDIR)
	$(RM) fifo.check fifo/
#	$(RM) -r delta_counter.check delta_counter/
	$(RM) counter.check counter/
	$(RM) fall_through_register.check fall_through_register/
	$(RM) cdc_reset_ctrlr_half.check cdc_reset_ctrlr_half/
	$(RM) cdc_reset_ctrlr_composed.check cdc_reset_ctrlr_composed/

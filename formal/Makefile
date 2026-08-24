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

YOSYS  ?= yosys
SBY    ?= sby
BENDER ?= bender
FLOCK  ?= flock
RM     = rm -rf

FORMAL_BUILDDIR ?= build
FORMAL_FLIST   := $(FORMAL_BUILDDIR)/formal.flist
FORMAL_TARGETS := fifo counter delta_counter fall_through_register lzc \
	cdc_reset_ctrlr_half cdc_reset_ctrlr_composed heaviside

all: $(FORMAL_TARGETS:%=%.check)

$(FORMAL_BUILDDIR):
	mkdir -p $@

# Bender owns formal source selection. The forced prerequisite deliberately
# rewrites the shared list on every requested invocation, invalidating stale
# success markers after any source edit.
$(FORMAL_FLIST): FORCE | $(FORMAL_BUILDDIR)
	$(FLOCK) $(FORMAL_BUILDDIR)/formal.flist.lock sh -ec \
		'cd ..; $(BENDER) checkout; \
		 $(BENDER) script flist-plus -t formal -t cc_no_deprecated \
		 > $(abspath $@).tmp; mv $(abspath $@).tmp $(abspath $@)'

# Public .check aliases retain the historical interface. The real success
# marker is kept alongside the solver output in build/<target>/<target>.check.
fifo.check: $(FORMAL_BUILDDIR)/fifo/fifo.check

$(FORMAL_BUILDDIR)/fifo/fifo.check: fifo.sby $(FORMAL_FLIST) | $(FORMAL_BUILDDIR)
	mkdir -p $(dir $@)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/fifo/prove $< prove
	$(SBY) -f -d $(FORMAL_BUILDDIR)/fifo/cover $< cover
	touch $@

counter.check: $(FORMAL_BUILDDIR)/counter/counter.check

$(FORMAL_BUILDDIR)/counter/counter.check: counter.sby $(FORMAL_FLIST) | $(FORMAL_BUILDDIR)
	mkdir -p $(dir $@)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/counter/prove $< prove
	$(SBY) -f -d $(FORMAL_BUILDDIR)/counter/cover $< cover
	touch $@

delta_counter.check: $(FORMAL_BUILDDIR)/delta_counter/delta_counter.check

$(FORMAL_BUILDDIR)/delta_counter/delta_counter.check: delta_counter.sby $(FORMAL_FLIST) | $(FORMAL_BUILDDIR)
	mkdir -p $(dir $@)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/delta_counter/prove $< prove
	$(SBY) -f -d $(FORMAL_BUILDDIR)/delta_counter/cover $< cover
	touch $@

fall_through_register.check: $(FORMAL_BUILDDIR)/fall_through_register/fall_through_register.check

$(FORMAL_BUILDDIR)/fall_through_register/fall_through_register.check: \
		fall_through_register.sby $(FORMAL_FLIST) | $(FORMAL_BUILDDIR)
	mkdir -p $(dir $@)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/fall_through_register/prove $< prove
	$(SBY) -f -d $(FORMAL_BUILDDIR)/fall_through_register/cover $< cover
	touch $@

lzc.check: $(FORMAL_BUILDDIR)/lzc/lzc.check

$(FORMAL_BUILDDIR)/lzc/lzc.check: lzc.sby $(FORMAL_FLIST) | $(FORMAL_BUILDDIR)
	mkdir -p $(dir $@)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/lzc $<
	touch $@

cdc_reset_ctrlr_half.check: $(FORMAL_BUILDDIR)/cdc_reset_ctrlr_half/cdc_reset_ctrlr_half.check

$(FORMAL_BUILDDIR)/cdc_reset_ctrlr_half/cdc_reset_ctrlr_half.check: \
		cdc_reset_ctrlr_half.sby $(FORMAL_FLIST) | $(FORMAL_BUILDDIR)
	mkdir -p $(dir $@)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/cdc_reset_ctrlr_half/prove $< prove
	$(SBY) -f -d $(FORMAL_BUILDDIR)/cdc_reset_ctrlr_half/cover $< cover
	touch $@

cdc_reset_ctrlr_composed.check: $(FORMAL_BUILDDIR)/cdc_reset_ctrlr_composed/cdc_reset_ctrlr_composed.check

$(FORMAL_BUILDDIR)/cdc_reset_ctrlr_composed/cdc_reset_ctrlr_composed.check: \
		cdc_reset_ctrlr_composed.sby $(FORMAL_FLIST) | $(FORMAL_BUILDDIR)
	mkdir -p $(dir $@)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/cdc_reset_ctrlr_composed/prove $< prove
	$(SBY) -f -d $(FORMAL_BUILDDIR)/cdc_reset_ctrlr_composed/cover $< cover
	touch $@

heaviside.check: $(FORMAL_BUILDDIR)/heaviside/heaviside.check

$(FORMAL_BUILDDIR)/heaviside/heaviside.check: heaviside.sby $(FORMAL_FLIST) | $(FORMAL_BUILDDIR)
	mkdir -p $(dir $@)
	$(SBY) -f -d $(FORMAL_BUILDDIR)/heaviside $<
	touch $@

.PHONY: all clean FORCE $(FORMAL_TARGETS:%=%.check)

FORCE:

clean:
	$(RM) $(FORMAL_BUILDDIR)

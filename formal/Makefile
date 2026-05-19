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
RM	?= rm

all: fifo.check counter.check fall_through_register.check cdc_reset_ctrlr_half.check \
	cdc_reset_ctrlr_composed.check

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

cdc_reset_ctrlr_half.check: cdc_reset_ctrlr_half.sby cc_cdc_reset_ctrlr_half_properties.sv \
				../src/cc_cdc_reset_ctrlr.sv ../src/cc_cdc_4phase.sv \
				../src/cc_sync.sv ../src/cc_pkg.sv
	./run_cdc_reset_ctrlr_half.sh
	touch $@

cdc_reset_ctrlr_composed.check: cdc_reset_ctrlr_composed.sby cc_cdc_reset_ctrlr_properties.sv \
				cc_cdc_reset_ctrlr_half_properties.sv \
				../src/cc_cdc_reset_ctrlr.sv ../src/cc_cdc_4phase.sv \
				../src/cc_sync.sv ../src/cc_pkg.sv
	./run_cdc_reset_ctrlr_composed.sh
	touch $@

.PHONY: clean
clean:
	$(RM) -r fifo.check fifo/
#	$(RM) -r delta_counter.check delta_counter/
	$(RM) -r counter.check counter/
	$(RM) -r fall_through_register.check fall_through_register/
	$(RM) -r cdc_reset_ctrlr_half.check cdc_reset_ctrlr_half/
	$(RM) -r cdc_reset_ctrlr_composed.check cdc_reset_ctrlr_composed/

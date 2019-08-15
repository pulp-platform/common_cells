# Copyright (c) 2019 ETH Zurich, University of Bologna
#
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.

# Author: Robert Balas <balasr@iis.ee.ethz.ch>

YOSYS	?= yosys
SBY	?= sby
RM	?= rm

all: fifo_v3.check

fifo_v3.check: fifo_v3.sby ../src/fifo_v3.sv fifo_v3_properties.sv
	$(SBY) -f $<
	touch $@

.PHONY: clean
clean:
	$(RM) -r fifo_v3.check fifo_v3/

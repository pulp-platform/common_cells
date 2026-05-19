#!/usr/bin/env bash
# Copyright 2026 ETH Zurich and University of Bologna.
#
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License. You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
# Authors:
# - Philippe Sauter <phsauter@iis.ee.ethz.ch>
#
# Description: Composed Reset-Controller Proof Runner
# Run the composed reset-controller SymbiYosys proof from the formal directory.

set -euo pipefail

cd "$(dirname "$0")"
"${SBY:=sby}" -f cdc_reset_ctrlr_composed.sby

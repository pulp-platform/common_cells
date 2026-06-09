#!/usr/bin/env bash
# Copyright (c) 2014-2018 ETH Zurich, University of Bologna
#
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.

set -e

# If the VSIM environment variable is unset, default to the standard 'vsim' command.
[ ! -z "$VSIM" ] || VSIM=vsim

# Simulation arguments
TB_TOP=cc_rr_arb_tree_tb
VOPT_ARGS="+acc +cover=bcesfx"
SUPPRESS_ID=vsim-3009

GUI_MODE=0

# Exploration parameters
NUM_INPUTS=5 # Set to 5 as FlooNoC router

# Define a reusable function to run individual simulation sessions.
call_vsim() {
  if [[ $GUI_MODE -eq 1 ]]; then
    # Run in GUI mode.
    "$VSIM" "$@"
  else
    # Run in batch mode.
    echo "run -all" | "$VSIM" "$@" | tee vsim.log 2>&1

    # Search the log for QuestaSim successful completion string.
    grep "Errors: 0," vsim.log
  fi
}

# Use Bender (RTL dependency manager) to generate a QuestaSim compilation TCL script.
# The "-t test" flag ensures that simulation-only testbenches are included.
bender script vsim -t test > compile.tcl

# Compiles RTL and testbench modules, then launch the simulator in command-line mode (-c).
"$VSIM" -c -quiet -do 'source compile.tcl; quit'

# Run the RRA simulation with 1, 4, and 7 inputs respectively.
call_vsim "$TB_TOP" -GNumInp=$NUM_INPUTS -coverage -voptargs="$VOPT_ARGS" -suppress "$SUPPRESS_ID"
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
# Description: Four-Phase CDC Simulation Sweep
# Compile the test target and run plain plus timed-delay Questa regressions for
# cc_cdc_4phase.

set -euo pipefail

: "${BENDER:=bender}"
: "${VSIM:=vsim}"

read -r -a bender_cmd <<< "${BENDER}"
read -r -a vsim_cmd <<< "${VSIM}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
build_dir="${CDC_4PHASE_BUILDDIR:-${repo_root}/build/vsim/cdc_4phase}"
compile_tcl="${build_dir}/compile.tcl"

mkdir -p "${build_dir}"

cd "${repo_root}"
"${bender_cmd[@]}" checkout
"${bender_cmd[@]}" script vsim -t test -t tb > "${compile_tcl}"

cd "${build_dir}"
"${vsim_cmd[@]}" -c -quiet -do "source ${compile_tcl}; quit"

call_vsim() {
  local name="$1"
  local log_file="vsim.${name}.log"
  shift
  echo "== ${name} =="
  # Questa 10.7 reports the enum-typed RESET_MSG parameter default in
  # cc_cdc_4phase_src as a suppressible elaboration error, even though the
  # reset controller overrides it with an enum value.
  "${vsim_cmd[@]}" -c -quiet cc_cdc_4phase_tb -suppress 8386 "$@" -do 'run -all; quit -f' |
    tee "${log_file}"
  grep "Errors: 0," "${log_file}"
}

call_vsim decoupled_default \
  -gSEED=1 \
  -gNUM_RANDOM_TRANSFERS=100

call_vsim coupled_default \
  -gSEED=2 \
  -gDECOUPLED=0 \
  -gNUM_RANDOM_TRANSFERS=100

call_vsim reset_message \
  -gSEED=3 \
  -gSEND_RESET_MSG=1 \
  -gNUM_RANDOM_TRANSFERS=80

call_vsim src_fast \
  -gSEED=4 \
  -gNUM_RANDOM_TRANSFERS=100 \
  -gTCK_SRC_PS=5000 \
  -gTCK_DST_PS=17000

call_vsim dst_fast \
  -gSEED=5 \
  -gNUM_RANDOM_TRANSFERS=100 \
  -gTCK_SRC_PS=17000 \
  -gTCK_DST_PS=5000

call_vsim timed_decoupled_800ps \
  -gSEED=11 \
  -gNUM_RANDOM_TRANSFERS=80 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=800 \
  -gTCK_SRC_PS=10000 \
  -gTCK_DST_PS=10000

call_vsim timed_coupled_800ps \
  -gSEED=12 \
  -gDECOUPLED=0 \
  -gNUM_RANDOM_TRANSFERS=80 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=800 \
  -gTCK_SRC_PS=10000 \
  -gTCK_DST_PS=10000

call_vsim timed_reset_message_800ps \
  -gSEED=13 \
  -gSEND_RESET_MSG=1 \
  -gNUM_RANDOM_TRANSFERS=60 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=800 \
  -gTCK_SRC_PS=10000 \
  -gTCK_DST_PS=10000

call_vsim timed_relprime_offset_2200ps \
  -gSEED=14 \
  -gNUM_RANDOM_TRANSFERS=80 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=2200 \
  -gTCK_SRC_PS=7000 \
  -gTCK_DST_PS=11000 \
  -gSRC_START_DELAY_PS=1500 \
  -gDST_START_DELAY_PS=3300

call_vsim timed_src_fast_near_bound \
  -gSEED=15 \
  -gNUM_RANDOM_TRANSFERS=80 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=4500 \
  -gTCK_SRC_PS=5000 \
  -gTCK_DST_PS=17000 \
  -gSRC_START_DELAY_PS=1000 \
  -gDST_START_DELAY_PS=2500

call_vsim timed_dst_fast_near_bound \
  -gSEED=16 \
  -gNUM_RANDOM_TRANSFERS=80 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=4500 \
  -gTCK_SRC_PS=17000 \
  -gTCK_DST_PS=5000 \
  -gSRC_START_DELAY_PS=2500 \
  -gDST_START_DELAY_PS=1000

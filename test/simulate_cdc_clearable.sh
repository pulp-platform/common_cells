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
# Description: Clearable Two-Phase CDC Simulation Sweep
# Compile the test target and run plain plus timed-delay Questa regressions for
# cc_cdc_2phase_clearable.

set -euo pipefail

: "${BENDER:=bender}"
: "${VSIM:=vsim}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
build_dir="${CDC_CLEARABLE_BUILDDIR:-${repo_root}/build/vsim/cdc_clearable}"
compile_tcl="${build_dir}/compile.tcl"

mkdir -p "${build_dir}"

cd "${repo_root}"
"${BENDER}" script vsim -t test > "${compile_tcl}"

cd "${build_dir}"
"${VSIM}" -c -quiet -do "source ${compile_tcl}; quit"

call_vsim() {
  local name="$1"
  local log_file="vsim.${name}.log"
  shift
  echo "== ${name} =="
  # Questa 10.7 reports the enum-typed RESET_MSG parameter default in
  # cc_cdc_4phase_src as a suppressible elaboration error, even though the
  # reset controller overrides it with an enum value.
  "${VSIM}" -c -quiet cc_cdc_2phase_clearable_tb -suppress 8386 "$@" -do 'run -all; quit -f' |
    tee "${log_file}"
  grep "Errors: 0," "${log_file}"
}

call_vsim smoke_default \
  -gSEED=1 \
  -gNUM_RANDOM_TRANSFERS=100 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=120 \
  -gNUM_ACTIVE_STRESS_EVENTS=8

call_vsim src_fast \
  -gSEED=2 \
  -gNUM_RANDOM_TRANSFERS=100 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=120 \
  -gNUM_ACTIVE_STRESS_EVENTS=8 \
  -gTCK_SRC_PS=5000 \
  -gTCK_DST_PS=17000

call_vsim dst_fast \
  -gSEED=3 \
  -gNUM_RANDOM_TRANSFERS=100 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=120 \
  -gNUM_ACTIVE_STRESS_EVENTS=8 \
  -gTCK_SRC_PS=17000 \
  -gTCK_DST_PS=5000

call_vsim no_async_reset_sync_only \
  -gSEED=4 \
  -gCLEAR_ON_ASYNC_RESET=0 \
  -gSYNC_STAGES=2 \
  -gNUM_RANDOM_TRANSFERS=100 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=120 \
  -gNUM_ACTIVE_STRESS_EVENTS=8

call_vsim timed_balanced_250ps \
  -gSEED=11 \
  -gNUM_RANDOM_TRANSFERS=60 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=60 \
  -gNUM_ACTIVE_STRESS_EVENTS=4 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=250 \
  -gTCK_SRC_PS=10000 \
  -gTCK_DST_PS=10000

call_vsim timed_src_fast_800ps \
  -gSEED=12 \
  -gNUM_RANDOM_TRANSFERS=60 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=60 \
  -gNUM_ACTIVE_STRESS_EVENTS=4 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=800 \
  -gTCK_SRC_PS=5000 \
  -gTCK_DST_PS=17000

call_vsim timed_dst_fast_800ps \
  -gSEED=13 \
  -gNUM_RANDOM_TRANSFERS=60 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=60 \
  -gNUM_ACTIVE_STRESS_EVENTS=4 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=800 \
  -gTCK_SRC_PS=17000 \
  -gTCK_DST_PS=5000

call_vsim timed_no_async_reset_sync_only \
  -gSEED=10 \
  -gCLEAR_ON_ASYNC_RESET=0 \
  -gSYNC_STAGES=2 \
  -gNUM_RANDOM_TRANSFERS=60 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=60 \
  -gNUM_ACTIVE_STRESS_EVENTS=4 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=800

call_vsim timed_balanced_offset_1800ps \
  -gSEED=14 \
  -gNUM_RANDOM_TRANSFERS=80 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=80 \
  -gNUM_ACTIVE_STRESS_EVENTS=5 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=1800 \
  -gTCK_SRC_PS=10000 \
  -gTCK_DST_PS=10000 \
  -gDST_START_DELAY_PS=2500

call_vsim timed_relprime_offset_2200ps \
  -gSEED=15 \
  -gNUM_RANDOM_TRANSFERS=80 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=80 \
  -gNUM_ACTIVE_STRESS_EVENTS=5 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=2200 \
  -gTCK_SRC_PS=7000 \
  -gTCK_DST_PS=11000 \
  -gSRC_START_DELAY_PS=1500 \
  -gDST_START_DELAY_PS=3300

call_vsim timed_src_fast_near_bound \
  -gSEED=16 \
  -gNUM_RANDOM_TRANSFERS=80 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=80 \
  -gNUM_ACTIVE_STRESS_EVENTS=5 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=4500 \
  -gTCK_SRC_PS=5000 \
  -gTCK_DST_PS=17000 \
  -gSRC_START_DELAY_PS=1000 \
  -gDST_START_DELAY_PS=2500

call_vsim timed_dst_fast_near_bound \
  -gSEED=17 \
  -gNUM_RANDOM_TRANSFERS=80 \
  -gNUM_ACTIVE_STRESS_TRANSFERS=80 \
  -gNUM_ACTIVE_STRESS_EVENTS=5 \
  -gINJECT_DELAYS=1 \
  -gMAX_DELAY_PS=4500 \
  -gTCK_SRC_PS=17000 \
  -gTCK_DST_PS=5000 \
  -gSRC_START_DELAY_PS=2500 \
  -gDST_START_DELAY_PS=1000

// Copyright 2026 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51
//
// Description: Deprecated register macro aliases kept for backward compatibility.
//   Included from common_cells/registers.svh AFTER `FF and `FFL are defined.
//   `FFARN  is identical to `FF  (asynchronous active-low reset)
//   `FFLARN is identical to `FFL (load-enable, asynchronous active-low reset)
//
//   Pass the bender target 'cc_no_deprecated' (define TARGET_CC_NO_DEPRECATED) to
//   compile this file as empty and enforce use of the non-deprecated macros.

`ifndef COMMON_CELLS_REGISTERS_DEPRECATED_SVH_
`define COMMON_CELLS_REGISTERS_DEPRECATED_SVH_

`ifndef TARGET_CC_NO_DEPRECATED

// `FFARN: asynchronous active-low reset (alias of `FF)
`define FFARN(__q, __d, __reset_value, __clk = `REG_DFLT_CLK, __arst_n = `REG_DFLT_RST_N) \
  `FF(__q, __d, __reset_value, __clk, __arst_n)                                            \
  /* synopsys translate_off */                                                            \
  initial $warning("Macro 'FFARN' is deprecated. Use 'FF' instead.");                      \
  /* synopsys translate_on */

// `FFLARN: load-enable, asynchronous active-low reset (alias of `FFL)
`define FFLARN(__q, __d, __load, __reset_value, __clk = `REG_DFLT_CLK, __arst_n = `REG_DFLT_RST_N) \
  `FFL(__q, __d, __load, __reset_value, __clk, __arst_n)                                            \
  /* synopsys translate_off */                                                                      \
  initial $warning("Macro 'FFLARN' is deprecated. Use 'FFL' instead.");                             \
  /* synopsys translate_on */

`endif // TARGET_CC_NO_DEPRECATED

`endif

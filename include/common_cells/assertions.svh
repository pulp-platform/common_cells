// Copyright 2020 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Stefan Mach <smach@iis.ee.ethz.ch>

// Common assertion and coverage defines for RTL designs
`ifndef COMMON_CELLS_ASSERTIONS_SVH_
`define COMMON_CELLS_ASSERTIONS_SVH_

// Abridged Summary of available assertion and coverage macros:
// `ASSERT:         immediate
// `ASSERT_ERR:     immediate with custom error message
// `ASSERTC:        concurrent clocked with implicit clock and reset
// `ASSERTC_ERR:    concurrent clocked with implicit clock and reset and custom error message
// `ASSERTC_CR:     concurrent clocked
// `ASSERTC_CRERR:  concurrent clocked with custom error message


// Immediate assertion
// __cond: Boolean expression that is asserted
// __label: Label to give this assertion
`define ASSERT(__cond, __label) \
  /``* pragma translate_off *``/ \
`ifndef VERILATOR \
  initial begin \
    __label : assert (__cond) else $error(`"__cond`"); \
  end \
`endif \
  /``* pragma translate_on *``/

// Immediate assertion with custom error message
// __cond: Boolean expression that is asserted
// __err: String containing the error message
// __label: Label to give this assertion
`define ASSERT_ERR(__cond, __err, __label) \
  /``* pragma translate_off *``/ \
`ifndef VERILATOR \
  initial begin \
    __label : assert (__cond) else $error(`"__err`"); \
  end \
`endif \
  /``* pragma translate_on *``/

// Concurrent clocked assertion with implicit clock and reset
// __prop: Property expression
// __label: Label to give this assertion
// Implicit:
// clk_i: clock signal
// rst_ni: reset signal (active low)
`define ASSERTC(__prop, __label) \
  /``* pragma translate_off *``/ \
`ifndef VERILATOR \
  __label : assert property (@(posedge clk_i) disable iff (!rst_ni) \
                             __prop) \
      else $error(`"__prop`"); \
`endif \
  /``* pragma translate_on *``/

// Concurrent clocked assertion with implicit clock and reset and custom error message
// __prop: Property expression
// __err: String containing the error message
// __label: Label to give this assertion
// Implicit:
// clk_i: clock signal
// rst_ni: reset signal (active low)
`define ASSERTC_ERR(__prop, __err, __label) \
  /``* pragma translate_off *``/ \
`ifndef VERILATOR \
  __label : assert property (@(posedge clk_i) disable iff (!rst_ni) \
                             __prop) \
      else $error(`"__err`"); \
`endif \
  /``* pragma translate_on *``/

// Concurrent clocked assertion
// __prop: Property expression
// __clk: clock signal
// __rstn: reset signal (active low)
// __label: Label to give this assertion
`define ASSERTC_CR(__prop, __clk, __rstn, __label) \
  /``* pragma translate_off *``/ \
`ifndef VERILATOR \
  __label : assert property (@(posedge __clk) disable iff (!__rstn) \
                             __prop) \
      else $error(`"__prop`"); \
`endif \
  /``* pragma translate_on *``/

// Concurrent clocked assertion with custom error message
// __prop: Property expression
// __err: String containing the error message
// __clk: clock signal
// __rstn: reset signal (active low)
// __label: Label to give this assertion
`define ASSERTC_CRERR(__prop, __clk, __rstn, __err, __label) \
  /``* pragma translate_off *``/ \
`ifndef VERILATOR \
  __label : assert property (@(posedge __clk) disable iff (!__rstn) \
                             __prop) \
      else $error(`"__err`"); \
`endif \
  /``* pragma translate_on *``/

`endif


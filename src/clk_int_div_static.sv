//-----------------------------------------------------------------------------
// Title         : Static Integer Clock Divider
//-----------------------------------------------------------------------------
// File          : clk_int_div_static.sv
// Author        : Manuel Eggimann  <meggimann@iis.ee.ethz.ch>
// Created       : 08.05.2023
//-----------------------------------------------------------------------------
// Description :
//
// This module implements a static arbitrary integer divider. Static in this
// case means, the divider value is constant at elaboration time (SV parameter).
// It supports arbitrary integer division with a guaranteed 50% duty cycle for
// odd and even division.

// Internally, this module is wrapper around the "at-runtime" configurable
// `clk_int_div`module. If you need to change the division factor at-runtime you
// should directly use `clk_int_div`instead. However if all you need is a single
// division factor this module provides a convenience wrapper for you with a
// simplified interface.
//
// The `en_i` signal can be used to enable or disable the output clock in a safe
// manner (there is an internal, glitch-free clock gate).
//
// Parameters:
//
// DIV_VALUE: The integer value by which the clock shall be divided. Must be
// non-zero integer smaller than 2^32-1.
//
// ENABLE_CLOCK_IN_RESET: If 1'b1, the clock gate will be enabled during reset
// which allows the clk_int_div instance to bypass the clock during reset, IFF
// the DEFAULT_DIV_VALUE is 1. For all other DEFAULT_DIV_VALUES, the output
// clock will not be available until rst_ni is deasserted!
//
// IMPORTANT!!!
//
// All clock gating/logic within this design is performed by dedicated clock
// logic tech cells. By default the common_cell library uses the behavioral
// models in the `tech_cells_generic` repository. However, for synthesis these
// cells need to be mapped to dedicated cells from your standard cell library,
// preferably ones that are designed for clock logic (they have balanced rise
// and fall time). During synthesis you furthermore have to properly set
// `dont_touch` or `size_only` attributes to prevent the logic synthesizer from
// replacing those cells with regular logic gates which could end up being
// glitchty!
//
//-----------------------------------------------------------------------------
// Copyright (C) 2023 ETH Zurich, University of Bologna Copyright and related
// rights are licensed under the Solderpad Hardware License, Version 0.51 (the
// "License"); you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law or
// agreed to in writing, software, hardware and materials distributed under this
// License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, either express or implied. See the License for the specific
// language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51
// -----------------------------------------------------------------------------


module clk_int_div_static #(
  parameter int unsigned DIV_VALUE = 1,
  parameter bit ENABLE_CLOCK_IN_RESET = 1'b1
) (
  input logic  clk_i,
  input logic  rst_ni,
  input logic  en_i,
  input logic  test_mode_en_i,
  output logic clk_o
);
  if (DIV_VALUE == 0) begin : gen_elab_error
    $error("DIV_VALUE must be strictly larger than 0.");
  end

  localparam int unsigned DivValueWidth = $clog2(DIV_VALUE+1);

  logic [DivValueWidth-1:0] div_value;
  assign div_value = DIV_VALUE;

  clk_int_div #(
    .DIV_VALUE_WIDTH       ( DivValueWidth         ),
    .DEFAULT_DIV_VALUE     ( DIV_VALUE             ),
    .ENABLE_CLOCK_IN_RESET ( ENABLE_CLOCK_IN_RESET )
  ) i_clk_int_div (
    .clk_i,
    .rst_ni,
    .en_i,
    .test_mode_en_i,
    .div_i        ( div_value ),
    .div_valid_i  ( 1'b0      ),
    .div_ready_o  (           ),
    .clk_o,
    .cycl_count_o (           )
  );

endmodule

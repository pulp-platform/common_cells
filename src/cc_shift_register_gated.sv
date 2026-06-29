// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Description: A Simple shift register with ICG for arbitrary depth and types.

`include "common_cells/registers.svh"

module cc_shift_register_gated #(
  parameter int unsigned Depth = 32'd8,
  parameter type         data_t = logic
) (
  input  logic  clk_i,    // Clock
  input  logic  rst_ni,   // Asynchronous reset active low
  input  logic  clr_i,    // Synchronous clear active high

  input  logic  valid_i,
  input  data_t data_i,
  output logic  valid_o,
  output data_t data_o
);

  // Register of depth 0 is a wire.
  if (Depth == 0) begin : gen_pass_through

    assign valid_o = valid_i;
    assign data_o  = data_i;

  // It's a shift register if depth is greater than 0
  end else begin : gen_shift_register

    logic  [Depth-1:0] valid_d, valid_q;
    data_t [Depth-1:0] data_d, data_q;

    for (genvar i = 0; i < Depth; i++) begin : gen_regs

      // Prepare D port for each shift register.
      if (i == 0) begin : gen_shift_in
        assign valid_d[i] = valid_i;
        assign data_d[i]  = data_i;
      end else begin : gen_shift
        assign valid_d[i] = valid_q[i-1];
        assign data_d[i]  = data_q[i-1];
      end

      // shift valid flag without clock gate
      `FFARNC(valid_q[i], valid_d[i], clr_i, '0, clk_i, rst_ni)

      // Gate each shift register with a valid flag to enable the synthsis tools to insert ICG for
      // better power comsumption.
      `FFLARNC(data_q[i], data_d[i], valid_d[i], clr_i, data_t'('0), clk_i, rst_ni)
    end

    // Output the shifted result.
    assign valid_o = valid_q[Depth-1];
    assign data_o  = data_q[Depth-1];

  end

endmodule

// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "common_cells/registers.svh"

/// Register with a simple stream-like ready/valid handshake.
/// This register does not cut combinatorial paths on all control signals; if you need a complete
/// cut, use the `spill_register`.
module stream_register #(
    parameter type T = logic  // Vivado requires a default value for type parameters.
) (
    input  logic    clk_i,          // Clock
    input  logic    rst_ni,         // Asynchronous active-low reset
    input  logic    clr_i,          // Synchronous clear
    input  logic    testmode_i,     // Test mode to bypass clock gating
    // Input port
    input  logic    valid_i,
    output logic    ready_o,
    input  T        data_i,
    // Output port
    output logic    valid_o,
    input  logic    ready_i,
    output T        data_o
);

    logic reg_ena;
    assign ready_o = ready_i | ~valid_o;
    assign reg_ena = valid_i & ready_o;
    // Load-enable FFs with synch clear
    `FFLARNC(valid_o, valid_i, ready_o, clr_i, 1'b0, clk_i, rst_ni)
    `FFLARNC(data_o,   data_i, reg_ena, clr_i,   '0, clk_i, rst_ni)

endmodule

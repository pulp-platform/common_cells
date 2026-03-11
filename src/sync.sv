// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Antonio Pullini <pullinia@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

module sync #(
    parameter int unsigned STAGES = 2,
    parameter bit ResetValue = 1'b0
) (
    input  logic clk_i,
    input  logic rst_ni,
    input  logic clr_i,
    input  logic serial_i,
    output logic serial_o
);

    (* dont_touch = "true" *)
    (* async_reg = "true" *)
    logic [STAGES-1:0] reg_q;

    `FFARNC(reg_q, {reg_q[STAGES-2:0], serial_i}, clr_i, {STAGES{ResetValue}}, clk_i, rst_ni)

    assign serial_o = reg_q[STAGES-1];

endmodule

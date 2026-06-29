// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba, ETH Zurich
// Date: 5.11.2018
// Description: 16-bit LFSR

`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

// --------------
// 16-bit LFSR
// --------------
//
// Description: Shift register
//
module cc_lfsr_16bit #(
    parameter logic [15:0] Seed  = 8'b0,
    parameter int unsigned Width = 16
)(
    input  logic                      clk_i,  // Clock
    input  logic                      rst_ni, // Asynchronous reset active low
    input  logic                      clr_i,  // Synchronous clear active high
    input  logic                      en_i,
    output logic [Width-1:0]          refill_way_oh_o,
    output logic [$clog2(Width)-1:0]  refill_way_bin_o
);

    localparam int unsigned LogWidth = $clog2(Width);

    logic [15:0] shift_d, shift_q;


    always_comb begin

        automatic logic shift_in;
        shift_in = !(shift_q[15] ^ shift_q[12] ^ shift_q[5] ^ shift_q[1]);

        shift_d = shift_q;

        if (en_i)
            shift_d = {shift_q[14:0], shift_in};

        // output assignment
        refill_way_oh_o = 'b0;
        refill_way_oh_o[shift_q[LogWidth-1:0]] = 1'b1;
        refill_way_bin_o = shift_q;
    end

    `FFARNC(shift_q, shift_d, clr_i, Seed, clk_i, rst_ni)

  `ifndef COMMON_CELLS_ASSERTS_OFF
    `ASSERT_INIT(width_gt_16, Width <= 16,
                 "Width needs to be less than 16 because of the 16-bit LFSR")
  `endif

endmodule

// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Brian Bui <buiminhnhut114@gmail.com>

// Property checker applied to each instantiation of cc_heaviside.
// Proves that mask_o contains all and only the asserted bits in the
// [0, x_i] interval. Inputs greater than or equal to Width saturate the
// output to an all-ones mask.
module cc_heaviside_properties import cc_pkg::*; #(
    parameter int unsigned Width = 32,
    localparam int unsigned IdxWidth = cc_pkg::idx_width(Width),
    localparam type idx_t  = logic [IdxWidth-1:0],
    localparam type mask_t = logic [Width-1:0]
) (
    input idx_t  x_i,
    input mask_t mask_o
);

    // ---- Reference model ----
    // Compute the expected mask: bits [0 .. x_i] are 1, the rest are 0.
    // If unsigned'(x) >= Width, every output bit is set.
    function automatic mask_t expected_mask(input idx_t x);
        expected_mask = '0;
        for (int unsigned i = 0; i < Width; i++) begin
            if (i <= unsigned'(x)) begin
                expected_mask[i] = 1'b1;
            end
        end
    endfunction

    // The DUT output must match the reference model for every input.
    always_comb begin
        assert (mask_o == expected_mask(x_i));
    end

endmodule : cc_heaviside_properties

bind cc_heaviside cc_heaviside_properties #(
    .Width ( Width )
) i_cc_heaviside_properties (
    .x_i    ( x_i    ),
    .mask_o ( mask_o )
);

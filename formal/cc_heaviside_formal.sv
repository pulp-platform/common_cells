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

// Elaboration harness instantiating cc_heaviside over representative
// parametrizations including non-power-of-two widths.
module cc_heaviside_formal import cc_pkg::*; #(
    parameter int unsigned MaxWidth = 33
) (
    input logic [MaxWidth-1:0] dummy_i
);

    for (genvar width = 1; width <= MaxWidth; width++) begin : gen_width
        localparam int unsigned Width    = unsigned'(width);
        localparam int unsigned IdxWidth = cc_pkg::idx_width(Width);

        logic [IdxWidth-1:0] x;
        logic [Width-1:0]    mask;

        // Use the lower bits of the formal input as the index
        assign x = dummy_i[IdxWidth-1:0];

        cc_heaviside #(
            .Width ( Width )
        ) i_heaviside (
            .x_i    ( x    ),
            .mask_o ( mask )
        );
    end

endmodule : cc_heaviside_formal

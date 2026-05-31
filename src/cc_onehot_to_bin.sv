// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Franceco Conti <fconti@iis.ee.ethz.ch>

`include "common_cells/assertions.svh"

module cc_onehot_to_bin #(
    parameter int unsigned  OnehotWidth = 16,
    // Do Not Change
    localparam int unsigned BinWidth    = OnehotWidth == 1 ? 1 : $clog2(OnehotWidth)
)   (
    input  logic [OnehotWidth-1:0] onehot_i,
    output logic [BinWidth-1:0]    bin_o
);

    for (genvar j = 0; j < BinWidth; j++) begin : gen_jl
        logic [OnehotWidth-1:0] tmp_mask;
            for (genvar i = 0; i < OnehotWidth; i++) begin : gen_il
                logic [BinWidth-1:0] tmp_i;
                assign tmp_i = BinWidth'(i);
                assign tmp_mask[i] = tmp_i[j];
            end
        assign bin_o[j] = |(tmp_mask & onehot_i);
    end

`ifndef COMMON_CELLS_ASSERTS_OFF
    `ASSERT_FINAL(more_than_2_bits, $onehot0(onehot_i), "More than two bit set in the one-hot signal")
`endif
endmodule

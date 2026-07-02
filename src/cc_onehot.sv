// Copyright 2021 ETH Zurich.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/// Hardware implementation of SystemVerilog's `$onehot()` function.
/// It uses a tree of half adders and a separate
/// or reduction tree for the carry.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Author: Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Author: Stefan Mach <smach@iis.ee.ethz.ch>
module cc_onehot #(
  parameter int unsigned Width = 4
) (
  input  logic [Width-1:0] d_i,
  output logic is_onehot_o
);
  // trivial base case
  if (Width == 1) begin : gen_degenerated_onehot
    assign is_onehot_o = d_i;
  end else begin : gen_onehot
    localparam int unsigned Lvls = $clog2(Width) + 1;

    logic [Lvls-1:0][2**(Lvls-1)-1:0] sum, carry;
    logic [Lvls-2:0] carry_array;

    // Extend to a power of two.
    assign sum[0] = d_i;

    // generate half adders for each lvl
    // lvl 0 is the input level
    for (genvar i = 1; i < Lvls; i++) begin : gen_lvl
      localparam int unsigned LvlWidth = 2**Lvls / 2**i;
      for (genvar j = 0; j < LvlWidth; j+=2) begin : gen_width
        assign sum[i][j/2] = sum[i-1][j] ^ sum[i-1][j+1];
        assign carry[i][j/2] = sum[i-1][j] & sum[i-1][j+1];
      end
      // generate carry tree
      assign carry_array[i-1] = |carry[i][LvlWidth/2-1:0];
    end
    assign is_onehot_o = sum[Lvls-1][0] & ~|carry_array;
  end

endmodule

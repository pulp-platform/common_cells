// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Philippe Sauter <phsauter@iis.ee.ethz.ch>

// Property checker applied to each instantiation of cc_lzc
module cc_lzc_properties import cc_pkg::*; #(
    parameter int unsigned Width = 2,
    parameter lzc_mode_e   Mode  = LZC_LEADING_ZERO_CNT,
    localparam int unsigned CntWidth = cc_pkg::idx_width(Width)
) (
    input logic [Width-1:0]    in_i,
    input logic [CntWidth-1:0] cnt_o,
    input logic                empty_o
);

    function automatic logic [CntWidth-1:0] expected_cnt(input logic [Width-1:0] in);
        logic found;

        expected_cnt = '0;
        found = 1'b0;

        if (Mode == LZC_LEADING_ZERO_CNT) begin
            for (int unsigned i = 0; i < Width; i++) begin
                if (!found && in[Width-1-i]) begin
                    expected_cnt = (CntWidth)'(i);
                    found = 1'b1;
                end
            end
        end else begin
            for (int unsigned i = 0; i < Width; i++) begin
                if (!found && in[i]) begin
                    expected_cnt = (CntWidth)'(i);
                    found = 1'b1;
                end
            end
        end

        if (!found) begin
            // one-bit degenerate implementation reports the exact zero count
            expected_cnt = (Width == 1) ? (CntWidth)'(1) : (CntWidth)'(Width - 1);
        end
    endfunction

    always_comb begin
        assert (empty_o == ~(|in_i));
        assert (cnt_o == expected_cnt(in_i));
    end

endmodule : cc_lzc_properties

bind cc_lzc cc_lzc_properties #(
    .Width ( Width ),
    .Mode  ( Mode  )
) i_cc_lzc_properties (
    .in_i    ( in_i    ),
    .cnt_o   ( cnt_o   ),
    .empty_o ( empty_o )
);

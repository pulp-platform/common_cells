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

// Elaboration harness instantiating everything that will be checked
module cc_lzc_formal import cc_pkg::*; #(
    parameter int unsigned MaxWidth = 64
) (
    input logic [MaxWidth-1:0] in_i
);

    for (genvar width = 1; width <= MaxWidth; width++) begin : gen_width
        localparam int unsigned Width = unsigned'(width);
        localparam int unsigned CntWidth = cc_pkg::idx_width(Width);

        logic [CntWidth-1:0] leading_cnt;
        logic [CntWidth-1:0] trailing_cnt;
        logic                leading_empty;
        logic                trailing_empty;

        // instantiate both modes per width
        cc_lzc #(
            .Width ( Width ),
            .Mode  ( LZC_LEADING_ZERO_CNT )
        ) i_lzc_leading (
            .in_i    ( in_i[Width-1:0] ),
            .cnt_o   ( leading_cnt   ),
            .empty_o ( leading_empty )
        );

        cc_lzc #(
            .Width ( Width ),
            .Mode  ( LZC_TRAILING_ZERO_CNT )
        ) i_lzc_trailing (
            .in_i    ( in_i[Width-1:0] ),
            .cnt_o   ( trailing_cnt  ),
            .empty_o ( trailing_empty )
        );
    end

endmodule : cc_lzc_formal

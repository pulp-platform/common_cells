// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Warren Smith <233830950+repowazdogz-droid@users.noreply.github.com>

// Elaboration harness for the cc_ecc_encode / cc_ecc_decode pair.
//
// Per data width one encoder feeds four decoders, each seeing a different
// corruption of the encoded word, so every case in cc_ecc_properties.sv has
// its own precondition and none of them interfere.
//
// The default width set brackets every parity-width transition that proves in
// a few seconds. cc_pkg::ecc_get_parity_width adds a parity bit going from
// DataWidth 1 to 2, 4 to 5, and 11 to 12, so each of those boundaries is
// proved on both sides. 1, 4 and 11 are also the widths whose encoded word is
// exactly a power of two bits wide, the case where an index constraint is
// easiest to get wrong. Wider parametrizations, including the module default
// of 64, are covered by the `sweep` task; see formal/README.md.
module cc_ecc_formal import cc_pkg::*; #(
`ifdef ECC_FULL_SWEEP
    parameter  int unsigned NumWidths        = 11,
    parameter  int unsigned Widths [11]      = '{1, 2, 4, 5, 11, 12, 26, 27, 57, 58, 64},
`else
    parameter  int unsigned NumWidths        = 6,
    parameter  int unsigned Widths [6]       = '{1, 2, 4, 5, 11, 12},
`endif
    // Do not change
    localparam int unsigned MaxDataWidth     = Widths[NumWidths-1],
    localparam int unsigned MaxEncodedWidth  = cc_pkg::ecc_get_cw_width(MaxDataWidth) + 1,
    localparam int unsigned MaxIdxWidth      = cc_pkg::idx_width(MaxEncodedWidth)
) (
    /// Symbolic data word, one disjoint slice per width.
    input logic [NumWidths*MaxDataWidth-1:0] data_i,
    /// Symbolic positions of the injected bit flips, one disjoint slice per width.
    ///
    /// The slices must not overlap. Every width constrains its own positions to
    /// its own encoded word, so sharing bits between widths would let one
    /// width's assumption narrow another's reachable positions: the proof would
    /// still pass, having never exercised the excluded positions. The `cover`
    /// task is what makes that visible.
    input logic [NumWidths*MaxIdxWidth-1:0]  pos_a_i,
    input logic [NumWidths*MaxIdxWidth-1:0]  pos_b_i
);

  for (genvar w = 0; w < NumWidths; w++) begin : gen_width
    localparam int unsigned DataWidth   = Widths[w];
    localparam int unsigned ParityWidth = cc_pkg::ecc_get_parity_width(DataWidth);
    localparam int unsigned CwWidth     = cc_pkg::ecc_get_cw_width(DataWidth);
    localparam int unsigned TotWidth    = CwWidth + 1;
    localparam int unsigned IdxWidth    = cc_pkg::idx_width(TotWidth);

    logic [DataWidth-1:0] data;
    logic [IdxWidth-1:0]  pos_a, pos_b;

    assign data  = data_i [w*MaxDataWidth +: DataWidth];
    assign pos_a = pos_a_i[w*MaxIdxWidth  +: IdxWidth];
    assign pos_b = pos_b_i[w*MaxIdxWidth  +: IdxWidth];

    // ------------------------------------------------------------ encoder
    logic [TotWidth-1:0] encoded;

    cc_ecc_encode #(
        .DataWidth ( DataWidth )
    ) i_encode (
        .data_i ( data    ),
        .data_o ( encoded )
    );

    // -------------------------------------------------------- corruptions
    // One-hot masks built from the symbolic positions. The positions are
    // constrained to the encoded word in cc_ecc_properties.sv.
    logic [TotWidth-1:0] mask_a, mask_b;
    assign mask_a = {{(TotWidth-1){1'b0}}, 1'b1} << pos_a;
    assign mask_b = {{(TotWidth-1){1'b0}}, 1'b1} << pos_b;

    // The extended parity bit is the MSB of the packed {parity, code_word}.
    localparam logic [TotWidth-1:0] ParityMask = {1'b1, {CwWidth{1'b0}}};

    logic [TotWidth-1:0] word_clean, word_single, word_parity, word_double;
    assign word_clean  = encoded;
    assign word_single = encoded ^ mask_a;           // P2 restricts pos_a to the codeword
    assign word_parity = encoded ^ ParityMask;
    assign word_double = encoded ^ mask_a ^ mask_b;  // P4 restricts pos_a != pos_b

    // ------------------------------------------------------------ decoders
    logic [DataWidth-1:0] clean_data, sgl_data, par_data;
    logic clean_single, clean_parity, clean_double;
    logic sgl_single,   sgl_parity,   sgl_double;
    logic par_single,   par_parity,   par_double;
    logic dbl_single,   dbl_parity,   dbl_double;
    logic [ParityWidth-1:0] clean_syndrome, sgl_syndrome, par_syndrome, dbl_syndrome;

    cc_ecc_decode #(
        .DataWidth ( DataWidth )
    ) i_decode_clean (
        .data_i         ( word_clean    ),
        .data_o         ( clean_data    ),
        .syndrome_o     ( clean_syndrome ),
        .single_error_o ( clean_single  ),
        .parity_error_o ( clean_parity  ),
        .double_error_o ( clean_double  )
    );

    cc_ecc_decode #(
        .DataWidth ( DataWidth )
    ) i_decode_single (
        .data_i         ( word_single  ),
        .data_o         ( sgl_data     ),
        .syndrome_o     ( sgl_syndrome ),
        .single_error_o ( sgl_single   ),
        .parity_error_o ( sgl_parity   ),
        .double_error_o ( sgl_double   )
    );

    cc_ecc_decode #(
        .DataWidth ( DataWidth )
    ) i_decode_parity (
        .data_i         ( word_parity  ),
        .data_o         ( par_data     ),
        .syndrome_o     ( par_syndrome ),
        .single_error_o ( par_single   ),
        .parity_error_o ( par_parity   ),
        .double_error_o ( par_double   )
    );

    // data_o is left unconnected on purpose: the decoder promises nothing about
    // the recovered word under a double error, so no property may read it.
    cc_ecc_decode #(
        .DataWidth ( DataWidth )
    ) i_decode_double (
        .data_i         ( word_double  ),
        .data_o         (              ),
        .syndrome_o     ( dbl_syndrome ),
        .single_error_o ( dbl_single   ),
        .parity_error_o ( dbl_parity   ),
        .double_error_o ( dbl_double   )
    );

    // ---------------------------------------------------------- properties
    cc_ecc_properties #(
        .DataWidth ( DataWidth )
    ) i_properties (
        .data_i         ( data         ),
        .pos_a_i        ( pos_a        ),
        .pos_b_i        ( pos_b        ),
        .clean_data_i     ( clean_data     ),
        .clean_single_i   ( clean_single   ),
        .clean_parity_i   ( clean_parity   ),
        .clean_double_i   ( clean_double   ),
        .clean_syndrome_i ( clean_syndrome ),
        .sgl_data_i       ( sgl_data       ),
        .sgl_single_i     ( sgl_single     ),
        .sgl_parity_i     ( sgl_parity     ),
        .sgl_double_i     ( sgl_double     ),
        .sgl_syndrome_i   ( sgl_syndrome   ),
        .par_data_i       ( par_data       ),
        .par_single_i     ( par_single     ),
        .par_parity_i     ( par_parity     ),
        .par_double_i     ( par_double     ),
        .par_syndrome_i   ( par_syndrome   ),
        .dbl_single_i     ( dbl_single     ),
        .dbl_parity_i     ( dbl_parity     ),
        .dbl_double_i     ( dbl_double     ),
        .dbl_syndrome_i   ( dbl_syndrome   )
    );
  end

endmodule : cc_ecc_formal

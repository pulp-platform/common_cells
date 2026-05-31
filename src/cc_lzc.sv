// Copyright 2018 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/assertions.svh"

/// A trailing zero counter / leading zero counter.
/// Set MODE to LZC_TRAILING_ZERO_CNT for trailing zero counter => cnt_o is the number of trailing zeros (from the LSB)
/// Set MODE to LZC_LEADING_ZERO_CNT for leading zero counter  => cnt_o is the number of leading zeros  (from the MSB)
/// If the input does not contain a one, `empty_o` is asserted. Additionally `cnt_o` contains
/// the maximum number of zeros - 1. For example:
///   in_i = 000_0000, empty_o = 1, cnt_o = 6 (mode = LZC_TRAILING_ZERO_CNT)
///   in_i = 000_0001, empty_o = 0, cnt_o = 0 (mode = LZC_TRAILING_ZERO_CNT)
///   in_i = 000_1000, empty_o = 0, cnt_o = 3 (mode = LZC_TRAILING_ZERO_CNT)
/// Furthermore, this unit contains a more efficient implementation for Verilator (simulation only).
/// This speeds up simulation significantly.
module cc_lzc import cc_pkg::*; #(
  /// The width of the input vector.
  parameter int unsigned Width = 2,
  /// Trailing or leading zero mode selection
  parameter lzc_mode_e   Mode  = LZC_LEADING_ZERO_CNT,
  /// Dependent parameter. Do **not** change!
  ///
  /// Width of the output signal with the zero count.
  localparam int unsigned CntWidth = cc_pkg::idx_width(Width)
) (
  /// Input vector to be counted.
  input  logic [Width-1:0]    in_i,
  /// Count of the leading / trailing zeros.
  output logic [CntWidth-1:0] cnt_o,
  /// Counter is empty: Asserted if all bits in in_i are zero.
  output logic                empty_o
);

  `ifndef COMMON_CELLS_ASSERTS_OFF
    `ASSERT_INIT(width_0, Width > 0, "input must be at least one bit wide")
  `endif

  if (Width <= 1) begin : gen_degenerate_lzc

    assign cnt_o[0] = !in_i[0];
    assign empty_o = !in_i[0];

  end else begin : gen_lzc

    localparam int unsigned NumLevels = $clog2(Width);

    logic [Width-1:0][NumLevels-1:0] index_lut;
    logic [2**NumLevels-1:0] sel_nodes                  /* verilator split_var */;
    logic [2**NumLevels-1:0][NumLevels-1:0] index_nodes /* verilator split_var */;

    logic [Width-1:0] in_tmp;

    if (Mode == LZC_LEADING_ZERO_CNT) begin : g_flip
      // Mode 1 (leading zero): flip input vector
      always_comb begin : flip_vector
        for (int unsigned i = 0; i < Width; i++) begin
          in_tmp[i] = in_i[Width-1-i];
        end
      end
    end else begin : g_no_flip
      // Mode 0 (trailing zero)
      assign in_tmp = in_i;
    end

    for (genvar j = 0; unsigned'(j) < Width; j++) begin : g_index_lut
      assign index_lut[j] = (NumLevels)'(unsigned'(j));
    end

    for (genvar level = 0; unsigned'(level) < NumLevels; level++) begin : g_levels
      if (unsigned'(level) == NumLevels - 1) begin : g_last_level
        for (genvar k = 0; k < 2 ** level; k++) begin : g_level
          // if two successive indices are still in the vector...
          if (unsigned'(k) * 2 < Width - 1) begin : g_reduce
            assign sel_nodes[2 ** level - 1 + k] = in_tmp[k * 2] | in_tmp[k * 2 + 1];
            assign index_nodes[2 ** level - 1 + k] = (in_tmp[k * 2] == 1'b1)
              ? index_lut[k * 2] :
                index_lut[k * 2 + 1];
          end
          // if only the first index is still in the vector...
          if (unsigned'(k) * 2 == Width - 1) begin : g_base
            assign sel_nodes[2 ** level - 1 + k] = in_tmp[k * 2];
            assign index_nodes[2 ** level - 1 + k] = index_lut[k * 2];
          end
          // if index is out of range
          if (unsigned'(k) * 2 > Width - 1) begin : g_out_of_range
            assign sel_nodes[2 ** level - 1 + k] = 1'b0;
            assign index_nodes[2 ** level - 1 + k] = '0;
          end
        end
      end else begin : g_not_last_level
        for (genvar l = 0; l < 2 ** level; l++) begin : g_level
          assign sel_nodes[2 ** level - 1 + l] =
              sel_nodes[2 ** (level + 1) - 1 + l * 2] | sel_nodes[2 ** (level + 1) - 1 + l * 2 + 1];
          assign index_nodes[2 ** level - 1 + l] = (sel_nodes[2 ** (level + 1) - 1 + l * 2] == 1'b1)
            ? index_nodes[2 ** (level + 1) - 1 + l * 2] :
              index_nodes[2 ** (level + 1) - 1 + l * 2 + 1];
        end
      end
    end

    assign cnt_o = NumLevels > unsigned'(0) ? index_nodes[0] : {($clog2(Width)) {1'b0}};
    assign empty_o = NumLevels > unsigned'(0) ? ~sel_nodes[0] : ~(|in_i);

  end : gen_lzc

endmodule : cc_lzc

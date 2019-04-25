// Copyright (c) 2018 - 2019 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.

/// A trailing zero counter / leading zero counter.
/// Set MODE to 0 for trailing zero counter => cnt_o is the number of trailing zeros (from the LSB)
/// Set MODE to 1 for leading zero counter  => cnt_o is the number of leading zeros  (from the MSB)
/// If the input does not contain a zero, `empty_o` is asserted. Additionally `cnt_o` contains
/// the maximum number of zeros - 1. For example:
///   in_i = 000_0000, empty_o = 1, cnt_o = 6 (mode = 0)
///   in_i = 000_0001, empty_o = 0, cnt_o = 0 (mode = 0)
///   in_i = 000_1000, empty_o = 0, cnt_o = 3 (mode = 0)
/// Furthermore, this unit contains a more efficient implementation for Verilator (simulation only).
/// This speeds up simulation significantly.

module lzc #(
  /// The width of the input vector.
  parameter int unsigned WIDTH = 2,
  parameter bit          MODE  = 1'b0 // 0 -> trailing zero, 1 -> leading zero
) (
  input  logic [WIDTH-1:0]         in_i,
  output logic [$clog2(WIDTH)-1:0] cnt_o,
  output logic                     empty_o // asserted if all bits in in_i are zero
);

  localparam int unsigned NUM_LEVELS = $clog2(WIDTH);

  // pragma translate_off
  initial begin
    assert(WIDTH > 0) else $fatal("input must be at least one bit wide");
  end
  // pragma translate_on

  logic [WIDTH-1:0][NUM_LEVELS-1:0]          index_lut;
  logic [2**NUM_LEVELS-1:0]                  sel_nodes;
  logic [2**NUM_LEVELS-1:0][NUM_LEVELS-1:0]  index_nodes;

  logic [WIDTH-1:0] in_tmp;

  // reverse vector if required
  always_comb begin : flip_vector
    for (int unsigned i = 0; i < WIDTH; i++) begin
      in_tmp[i] = (MODE) ? in_i[WIDTH-1-i] : in_i[i];
    end
  end

  for (genvar j = 0; unsigned'(j) < WIDTH; j++) begin : g_index_lut
    assign index_lut[j] = NUM_LEVELS'(j);
  end

  for (genvar level = 0; unsigned'(level) < NUM_LEVELS; level++) begin : g_levels
    if (unsigned'(level) == NUM_LEVELS-1) begin : g_last_level
      for (genvar k = 0; k < 2**level; k++) begin : g_level
        // if two successive indices are still in the vector...
        if (unsigned'(k) * 2 < WIDTH-1) begin
          assign sel_nodes[2**level-1+k]   = in_tmp[k*2] | in_tmp[k*2+1];
          assign index_nodes[2**level-1+k] = (in_tmp[k*2] == 1'b1) ? index_lut[k*2] :
                                                                     index_lut[k*2+1];
        end
        // if only the first index is still in the vector...
        if (unsigned'(k) * 2 == WIDTH-1) begin
          assign sel_nodes[2**level-1+k]   = in_tmp[k*2];
          assign index_nodes[2**level-1+k] = index_lut[k*2];
        end
        // if index is out of range
        if (unsigned'(k) * 2 > WIDTH-1) begin
          assign sel_nodes[2**level-1+k]   = 1'b0;
          assign index_nodes[2**level-1+k] = '0;
        end
      end
    end else begin
      for (genvar l = 0; l < 2**level; l++) begin : g_level
        assign sel_nodes[2**level-1+l]   = sel_nodes[2**(level+1)-1+l*2] | sel_nodes[2**(level+1)-1+l*2+1];
        assign index_nodes[2**level-1+l] = (sel_nodes[2**(level+1)-1+l*2] == 1'b1) ? index_nodes[2**(level+1)-1+l*2] :
                                                                                     index_nodes[2**(level+1)-1+l*2+1];
      end
    end
  end

  assign cnt_o   = NUM_LEVELS > 0 ? index_nodes[0] : '0;
  assign empty_o = NUM_LEVELS > 0 ? ~sel_nodes[0]  : ~(|in_i);

endmodule : lzc

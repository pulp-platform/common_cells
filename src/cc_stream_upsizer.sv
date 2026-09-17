// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Lorenzo Leone <lleone@iis.ee.ethz.ch>

`include "common_cells/assertions.svh"

/// Stream upsizer: converts `WideWidth / NarrowWidth` consecutive narrow input beats
/// (valid-ready handshake) into one wide output beat.
module cc_stream_upsizer #(
  /// Data width of the narrow (input) side, in bits.
  parameter  int unsigned NarrowWidth = 32'd1,
  /// Data width of the wide (output) side, in bits. Must be an integer multiple of `NarrowWidth`.
  parameter  int unsigned WideWidth   = 32'd1,
  /// Number of narrow beats per wide beat (derived, do not override).
  localparam int unsigned Ratio       = WideWidth / NarrowWidth,
  /// Width of the internal slice counter (derived, do not override).
  localparam int unsigned CntWidth    = cc_pkg::idx_width(Ratio),
  /// Width of the register bank holding the non-final slices (derived, do not override).
  localparam int unsigned StoreWidth  = (Ratio - 1) * NarrowWidth
) (
  input  logic                   clk_i,
  input  logic                   rst_ni,
  /// Narrow input stream
  input  logic [NarrowWidth-1:0] inp_data_i,
  input  logic                   inp_valid_i,
  output logic                   inp_ready_o,
  /// Wide output stream
  output logic [  WideWidth-1:0] oup_data_o,
  output logic                   oup_valid_o,
  input  logic                   oup_ready_i
);

  `ASSERT_INIT(WidthRatio, (WideWidth % NarrowWidth == 0),
               "WideWidth must be an integer multiple of NarrowWidth")

  if (Ratio == 1) begin : gen_passthrough
    assign inp_ready_o = oup_ready_i;
    assign oup_valid_o = inp_valid_i;
    assign oup_data_o  = inp_data_i;
  end else begin : gen_upsize
    logic [CntWidth-1:0] slice_q;
    logic last_slice, accept;
    logic [StoreWidth-1:0] data_q;

    assign last_slice  = (slice_q == Ratio - 1);
    assign inp_ready_o = last_slice ? oup_ready_i : 1'b1;
    assign accept      = inp_valid_i && inp_ready_o;
    assign oup_valid_o = inp_valid_i && last_slice;
    assign oup_data_o  = {inp_data_i, data_q};

    // Counts which slice `inp_data_i` currently holds.
    cc_counter #(
      .Width         (CntWidth),
      .StickyOverflow(1'b0)
    ) i_slice_cnt (
      .clk_i,
      .rst_ni,
      .clr_i     (accept && last_slice),
      .en_i      (accept),
      .load_i    (1'b0),
      .down_i    (1'b0),
      .d_i       ('0),
      .q_o       (slice_q),
      .overflow_o(  /* unused: see comment above */)
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        data_q <= '0;
      end else if (accept && !last_slice) begin
        data_q[slice_q*NarrowWidth+:NarrowWidth] <= inp_data_i;
      end
    end
  end

endmodule : cc_stream_upsizer

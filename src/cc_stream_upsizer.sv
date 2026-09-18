// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Lorenzo Leone <lleone@iis.ee.ethz.ch>

`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

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

  if (Ratio == 1) begin : gen_passthrough
    assign inp_ready_o = oup_ready_i;
    assign oup_valid_o = inp_valid_i;
    assign oup_data_o  = inp_data_i;
  end else begin : gen_upsize
    logic [CntWidth-1:0] slice_q;
    logic last_slice, accept;
    logic [StoreWidth-1:0] data_q, data_d;

    assign inp_ready_o = last_slice ? oup_ready_i : 1'b1;
    assign accept      = inp_valid_i && inp_ready_o;
    assign oup_valid_o = inp_valid_i && last_slice;
    assign oup_data_o  = {inp_data_i, data_q};

    // Counts streamed slices.
    cc_trip_counter #(
      .Width(CntWidth)
    ) i_slice_cnt (
      .clk_i,
      .rst_ni,
      .clr_i  (1'b0),
      .en_i   (accept),
      .delta_i(CntWidth'(1)),
      .bound_i(CntWidth'(Ratio - 1)),
      .q_o    (slice_q),
      .last_o (last_slice),
      .trip_o (/* unused */)
    );

    always_comb begin
      data_d = data_q;
      if (accept && !last_slice) begin
        data_d[slice_q*NarrowWidth+:NarrowWidth] = inp_data_i;
      end
    end
    `FF(data_q, data_d, '0, clk_i, rst_ni)
  end

  `ASSERT_INIT(WidthRatio, (WideWidth % NarrowWidth == 0),
               "WideWidth must be an integer multiple of NarrowWidth")

endmodule : cc_stream_upsizer

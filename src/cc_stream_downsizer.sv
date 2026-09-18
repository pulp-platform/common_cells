// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Lorenzo Leone <lleone@iis.ee.ethz.ch>

`include "common_cells/assertions.svh"

/// Stream downsizer: converts one wide input beat (valid-ready handshake) into
/// `WideWidth / NarrowWidth` consecutive narrow output beats, LSB slice first.
module cc_stream_downsizer #(
  /// Data width of the narrow (output) side, in bits.
  parameter int unsigned NarrowWidth = 32'd1,
  /// Data width of the wide (input) side, in bits. Must be an integer multiple of `NarrowWidth`.
  parameter int unsigned WideWidth   = 32'd1
) (
  input  logic                   clk_i,
  input  logic                   rst_ni,
  /// Wide input stream
  input  logic [  WideWidth-1:0] inp_data_i,
  input  logic                   inp_valid_i,
  output logic                   inp_ready_o,
  /// Narrow output stream
  output logic [NarrowWidth-1:0] oup_data_o,
  output logic                   oup_valid_o,
  input  logic                   oup_ready_i
);

  /// Number of narrow beats per wide beat.
  localparam int unsigned Ratio    = WideWidth / NarrowWidth;
  /// Width of the internal slice counter.
  localparam int unsigned CntWidth = cc_pkg::idx_width(Ratio);

  logic [CntWidth-1:0] slice_q;

  assign oup_data_o  = inp_data_i[slice_q*NarrowWidth+:NarrowWidth];
  assign oup_valid_o = inp_valid_i;

  // Counts streamed slices.
  cc_trip_counter #(
    .Width(CntWidth)
  ) i_slice_cnt (
    .clk_i,
    .rst_ni,
    .clr_i  (1'b0),
    .en_i   (inp_valid_i && oup_ready_i),
    .delta_i(CntWidth'(1)),
    .bound_i(CntWidth'(Ratio - 1)),
    .q_o    (slice_q),
    .last_o (/* unused */),
    .trip_o (inp_ready_o)
  );

  `ASSERT_INIT(WidthRatio, (WideWidth % NarrowWidth == 0),
               "WideWidth must be an integer multiple of NarrowWidth")

endmodule : cc_stream_downsizer

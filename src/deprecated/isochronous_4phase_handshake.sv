// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_isochronous_4phase_handshake instead.

module isochronous_4phase_handshake (
  input  logic src_clk_i,
  input  logic src_rst_ni,
  input  logic src_valid_i,
  output logic src_ready_o,
  input  logic dst_clk_i,
  input  logic dst_rst_ni,
  input  logic dst_ready_i,
  output logic dst_valid_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_isochronous_4phase_handshake' instead.");
  // synthesis translate_on
  cc_isochronous_4phase_handshake i_cc_isochronous_4phase_handshake (
    .src_clk_i   ( src_clk_i   ),
    .src_rst_ni  ( src_rst_ni  ),
    .src_valid_i ( src_valid_i ),
    .src_ready_o ( src_ready_o ),
    .dst_clk_i   ( dst_clk_i   ),
    .dst_rst_ni  ( dst_rst_ni  ),
    .dst_ready_i ( dst_ready_i ),
    .dst_valid_o ( dst_valid_o )
  );
endmodule

// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_isochronous_spill_register instead.

module isochronous_spill_register #(
  parameter type T      = logic,
  parameter bit  Bypass = 1'b0
) (
  input  logic src_clk_i,
  input  logic src_rst_ni,
  input  logic src_valid_i,
  output logic src_ready_o,
  input  T     src_data_i,
  input  logic dst_clk_i,
  input  logic dst_rst_ni,
  input  logic dst_ready_i,
  output logic dst_valid_o,
  output T     dst_data_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_isochronous_spill_register' instead.");
  // synthesis translate_on
  cc_isochronous_spill_register #(
    .data_t ( T      ),
    .Bypass ( Bypass )
  ) i_cc_isochronous_spill_register (
    .src_clk_i   ( src_clk_i   ),
    .src_rst_ni  ( src_rst_ni  ),
    .src_valid_i ( src_valid_i ),
    .src_ready_o ( src_ready_o ),
    .src_data_i  ( src_data_i  ),
    .dst_clk_i   ( dst_clk_i   ),
    .dst_rst_ni  ( dst_rst_ni  ),
    .dst_ready_i ( dst_ready_i ),
    .dst_valid_o ( dst_valid_o ),
    .dst_data_o  ( dst_data_o  )
  );
endmodule

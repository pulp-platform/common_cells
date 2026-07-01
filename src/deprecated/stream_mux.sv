// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_mux instead.

module stream_mux #(
  parameter type    DATA_T    = logic,
  parameter integer N_INP     = 0,
  // Derived parameter (kept for backward compatibility, do not override)
  parameter integer SEL_WIDTH = cc_pkg::idx_width(N_INP)
) (
  input  DATA_T [N_INP-1:0]      inp_data_i,
  input  logic  [N_INP-1:0]      inp_valid_i,
  output logic  [N_INP-1:0]      inp_ready_o,
  input  logic  [SEL_WIDTH-1:0]  inp_sel_i,
  output DATA_T                  oup_data_o,
  output logic                   oup_valid_o,
  input  logic                   oup_ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_mux' instead.");
  // synthesis translate_on
  // Note: SEL_WIDTH is a localparam in cc_stream_mux, not passed.
  cc_stream_mux #(
    .data_t ( DATA_T ),
    .NumInp ( N_INP  )
  ) i_cc_stream_mux (
    .inp_data_i  ( inp_data_i  ),
    .inp_valid_i ( inp_valid_i ),
    .inp_ready_o ( inp_ready_o ),
    .inp_sel_i   ( inp_sel_i   ),
    .oup_data_o  ( oup_data_o  ),
    .oup_valid_o ( oup_valid_o ),
    .oup_ready_i ( oup_ready_i )
  );
endmodule

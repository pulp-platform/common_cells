// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_arbiter instead.

module stream_arbiter #(
  parameter type    DATA_T  = logic,
  parameter integer N_INP   = 1,
// verilog_lint: waive explicit-parameter-storage-type
  parameter         ARBITER = "rr"
) (
  input  logic               clk_i,
  input  logic               rst_ni,
  input  DATA_T [N_INP-1:0]  inp_data_i,
  input  logic  [N_INP-1:0]  inp_valid_i,
  output logic  [N_INP-1:0]  inp_ready_o,
  output DATA_T               oup_data_o,
  output logic                oup_valid_o,
  input  logic                oup_ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_arbiter' instead.");
  // synthesis translate_on
  localparam cc_pkg::arb_mode_e ArbMode =
    (ARBITER == "prio") ? cc_pkg::ARB_PRIO : cc_pkg::ARB_RR;
  cc_stream_arbiter #(
    .data_t  ( DATA_T  ),
    .NumInp  ( N_INP   ),
    .ArbMode ( ArbMode )
  ) i_cc_stream_arbiter (
    .clk_i       ( clk_i       ),
    .rst_ni      ( rst_ni      ),
    .clr_i       ( 1'b0        ),
    .inp_data_i  ( inp_data_i  ),
    .inp_valid_i ( inp_valid_i ),
    .inp_ready_o ( inp_ready_o ),
    .oup_data_o  ( oup_data_o  ),
    .oup_valid_o ( oup_valid_o ),
    .oup_ready_i ( oup_ready_i )
  );
endmodule

// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_rr_arb_tree instead.

module rr_arb_tree #(
  parameter int unsigned NumIn     = 64,
  parameter int unsigned DataWidth = 32,
  parameter type         DataType  = logic [DataWidth-1:0],
  parameter bit          ExtPrio   = 1'b0,
  parameter bit          AxiVldRdy = 1'b0,
  parameter bit          LockIn    = 1'b0,
  parameter bit          FairArb   = 1'b1,
  // Derived parameters (kept for backward compatibility, do not override)
  parameter int unsigned IdxWidth  = (NumIn > 32'd1) ? unsigned'($clog2(NumIn)) : 32'd1,
  parameter type         idx_t     = logic [IdxWidth-1:0]
) (
  input  logic               clk_i,
  input  logic               rst_ni,
  input  logic               flush_i,
  input  idx_t               rr_i,
  input  logic [NumIn-1:0]   req_i,
  output logic [NumIn-1:0]   gnt_o,
  input  DataType [NumIn-1:0] data_i,
  output logic               req_o,
  input  logic               gnt_i,
  output DataType            data_o,
  output idx_t               idx_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_rr_arb_tree' instead.");
  // synthesis translate_on
  // Note: IdxWidth and idx_t are localparams in cc_rr_arb_tree, not passed.
  cc_rr_arb_tree #(
    .NumIn     ( NumIn     ),
    .DataWidth ( DataWidth ),
    .data_t    ( DataType  ),
    .ExtPrio   ( ExtPrio   ),
    .AxiVldRdy ( AxiVldRdy ),
    .LockIn    ( LockIn    ),
    .FairArb   ( FairArb   )
  ) i_cc_rr_arb_tree (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .clr_i   ( flush_i ),
    .rr_i    ( rr_i    ),
    .req_i   ( req_i   ),
    .gnt_o   ( gnt_o   ),
    .data_i  ( data_i  ),
    .req_o   ( req_o   ),
    .gnt_i   ( gnt_i   ),
    .data_o  ( data_o  ),
    .idx_o   ( idx_o   )
  );
endmodule

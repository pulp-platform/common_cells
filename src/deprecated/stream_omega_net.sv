// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_omega_net instead.

module stream_omega_net #(
  parameter int unsigned NumInp      = 32'd0,
  parameter int unsigned NumOut      = 32'd0,
  parameter int unsigned Radix       = 32'd2,
  parameter int unsigned DataWidth   = 32'd1,
  parameter type         payload_t   = logic [DataWidth-1:0],
  parameter bit          SpillReg    = 1'b0,
  parameter int unsigned ExtPrio     = 1'b0,
  parameter int unsigned AxiVldRdy   = 1'b1,
  parameter int unsigned LockIn      = 1'b1,
  parameter payload_t    AxiVldMask  = '1,
  // Derived parameters (kept for backward compatibility, do not override)
  parameter int unsigned SelWidth    = (NumOut > 32'd1) ? unsigned'($clog2(NumOut)) : 32'd1,
  parameter type         sel_oup_t   = logic [SelWidth-1:0],
  parameter int unsigned IdxWidth    = (NumInp > 32'd1) ? unsigned'($clog2(NumInp)) : 32'd1,
  parameter type         idx_inp_t   = logic [IdxWidth-1:0]
) (
  input  logic                  clk_i,
  input  logic                  rst_ni,
  input  logic                  flush_i,
  input  idx_inp_t [NumOut-1:0] rr_i,
  input  payload_t [NumInp-1:0] data_i,
  input  sel_oup_t [NumInp-1:0] sel_i,
  input  logic     [NumInp-1:0] valid_i,
  output logic     [NumInp-1:0] ready_o,
  output payload_t [NumOut-1:0] data_o,
  output idx_inp_t [NumOut-1:0] idx_o,
  output logic     [NumOut-1:0] valid_o,
  input  logic     [NumOut-1:0] ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_omega_net' instead.");
  // synthesis translate_on
  // Note: SelWidth, sel_oup_t, IdxWidth, idx_inp_t are localparams in cc_stream_omega_net,
  //       not passed in instantiation.
  cc_stream_omega_net #(
    .NumInp    ( NumInp    ),
    .NumOut    ( NumOut    ),
    .Radix     ( Radix     ),
    .DataWidth ( DataWidth ),
    .payload_t ( payload_t ),
    .SpillReg  ( SpillReg  ),
    .ExtPrio   ( ExtPrio   ),
    .AxiVldRdy ( AxiVldRdy ),
    .LockIn    ( LockIn    ),
    .AxiVldMask( AxiVldMask)
  ) i_cc_stream_omega_net (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .flush_i ( flush_i ),
    .rr_i    ( rr_i    ),
    .data_i  ( data_i  ),
    .sel_i   ( sel_i   ),
    .valid_i ( valid_i ),
    .ready_o ( ready_o ),
    .data_o  ( data_o  ),
    .idx_o   ( idx_o   ),
    .valid_o ( valid_o ),
    .ready_i ( ready_i )
  );
endmodule

// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: `cc_stream_arbiter_flushable` has been merged into `cc_stream_arbiter`.
// Use `cc_stream_arbiter` with the `clr_i` port for flush functionality instead.

module cc_stream_arbiter_flushable #(
    parameter type               data_t  = logic,
    parameter int unsigned       NumInp  = 1,
    parameter cc_pkg::arb_mode_e ArbMode = cc_pkg::ARB_RR
) (
    input  logic               clk_i,
    input  logic               rst_ni,
    input  logic               flush_i,

    input  data_t [NumInp-1:0] inp_data_i,
    input  logic  [NumInp-1:0] inp_valid_i,
    output logic  [NumInp-1:0] inp_ready_o,

    output data_t              oup_data_o,
    output logic               oup_valid_o,
    input  logic               oup_ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_arbiter' instead, connecting 'flush_i' to 'clr_i'.");
  // synthesis translate_on

  cc_stream_arbiter #(
    .data_t  ( data_t  ),
    .NumInp  ( NumInp  ),
    .ArbMode ( ArbMode )
  ) i_cc_stream_arbiter (
    .clk_i       ( clk_i       ),
    .rst_ni      ( rst_ni      ),
    .clr_i       ( flush_i     ),
    .inp_data_i  ( inp_data_i  ),
    .inp_valid_i ( inp_valid_i ),
    .inp_ready_o ( inp_ready_o ),
    .oup_data_o  ( oup_data_o  ),
    .oup_valid_o ( oup_valid_o ),
    .oup_ready_i ( oup_ready_i )
  );

endmodule

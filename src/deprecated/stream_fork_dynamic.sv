// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_fork_dynamic instead.

module stream_fork_dynamic #(
  parameter int unsigned N_OUP = 32'd0
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             valid_i,
  output logic             ready_o,
  input  logic [N_OUP-1:0] sel_i,
  input  logic             sel_valid_i,
  output logic             sel_ready_o,
  output logic [N_OUP-1:0] valid_o,
  input  logic [N_OUP-1:0] ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_fork_dynamic' instead.");
  // synthesis translate_on
  cc_stream_fork_dynamic #(
    .NumOup ( N_OUP )
  ) i_cc_stream_fork_dynamic (
    .clk_i      ( clk_i      ),
    .rst_ni     ( rst_ni     ),
    .clr_i      ( 1'b0       ),
    .valid_i    ( valid_i    ),
    .ready_o    ( ready_o    ),
    .sel_i      ( sel_i      ),
    .sel_valid_i( sel_valid_i),
    .sel_ready_o( sel_ready_o),
    .valid_o    ( valid_o    ),
    .ready_i    ( ready_i    )
  );
endmodule

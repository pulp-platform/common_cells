// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_clk_mux_glitch_free instead.
module clk_mux_glitch_free #(
  parameter int unsigned NUM_INPUTS         = 2,
  parameter int unsigned NUM_SYNC_STAGES    = 2,
  parameter bit          CLOCK_DURING_RESET = 1'b1,
  localparam int unsigned SelWidth          = cc_pkg::idx_width(NUM_INPUTS)
)(
  input  logic [NUM_INPUTS-1:0] clks_i,
  input  logic                  test_clk_i,
  input  logic                  test_en_i,
  input  logic                  async_rstn_i,
  input  logic [SelWidth-1:0]   async_sel_i,
  output logic                  clk_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_clk_mux_glitch_free' instead.");
  // synthesis translate_on
  cc_clk_mux_glitch_free #(
    .NUM_INPUTS         ( NUM_INPUTS         ),
    .NUM_SYNC_STAGES    ( NUM_SYNC_STAGES    ),
    .CLOCK_DURING_RESET ( CLOCK_DURING_RESET )
  ) i_cc_clk_mux_glitch_free (
    .clks_i      ( clks_i      ),
    .test_clk_i  ( test_clk_i  ),
    .test_en_i   ( test_en_i   ),
    .async_rstn_i( async_rstn_i),
    .async_sel_i ( async_sel_i ),
    .clk_o       ( clk_o       )
  );
endmodule

// Deprecated: use cc_clk_or_tree instead.
module clk_or_tree #(
  parameter int unsigned NUM_INPUTS
)(
  input  logic [NUM_INPUTS-1:0] clks_i,
  output logic                  clk_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_clk_or_tree' instead.");
  // synthesis translate_on
  cc_clk_or_tree #(
    .NUM_INPUTS ( NUM_INPUTS )
  ) i_cc_clk_or_tree (
    .clks_i ( clks_i ),
    .clk_o  ( clk_o  )
  );
endmodule

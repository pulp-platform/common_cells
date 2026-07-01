// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_lfsr_8bit instead.

module lfsr_8bit #(
  parameter logic [7:0]  SEED  = 8'b0,
  parameter int unsigned WIDTH = 8
) (
  input  logic               clk_i,
  input  logic               rst_ni,
  input  logic               en_i,
  output logic [WIDTH-1:0]   refill_way_oh,
  output logic [$clog2(WIDTH)-1:0] refill_way_bin
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_lfsr_8bit' instead.");
  // synthesis translate_on
  cc_lfsr_8bit #(
    .Seed ( SEED  ),
    .Width ( WIDTH )
  ) i_cc_lfsr_8bit (
    .clk_i          ( clk_i          ),
    .rst_ni         ( rst_ni         ),
    .clr_i  ( 1'b0  ),
    .en_i           ( en_i           ),
    .refill_way_oh_o ( refill_way_oh  ),
    .refill_way_bin_o ( refill_way_bin )
  );
endmodule

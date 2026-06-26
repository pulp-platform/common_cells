// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_lfsr_16bit instead.

module lfsr_16bit #(
  parameter logic [15:0]  SEED  = 8'b0,
  parameter int unsigned  WIDTH = 16
) (
  input  logic               clk_i,
  input  logic               rst_ni,
  input  logic               en_i,
  output logic [WIDTH-1:0]   refill_way_oh,
  output logic [$clog2(WIDTH)-1:0] refill_way_bin
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_lfsr_16bit' instead.");
  // synthesis translate_on
  cc_lfsr_16bit #(
    .SEED  ( SEED  ),
    .WIDTH ( WIDTH )
  ) i_cc_lfsr_16bit (
    .clk_i          ( clk_i          ),
    .rst_ni         ( rst_ni         ),
    .en_i           ( en_i           ),
    .refill_way_oh  ( refill_way_oh  ),
    .refill_way_bin ( refill_way_bin )
  );
endmodule

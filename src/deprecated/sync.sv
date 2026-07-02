// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_sync instead.

module sync #(
  parameter int unsigned STAGES     = 2,
  parameter bit          ResetValue = 1'b0
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic serial_i,
  output logic serial_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'tc_sync' from 'tech_cells_generic' instead.");
  // synthesis translate_on
  logic [STAGES-1:0] serial_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      serial_q <= {STAGES{ResetValue}};
    end else begin
      serial_q <= {serial_q[STAGES-2:0], serial_i};
    end
  end
  assign serial_o = serial_q[STAGES-1];
endmodule

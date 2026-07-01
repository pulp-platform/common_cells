// Copyright 2018 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: cc_sync has been moved to the tech_cells_generic repository.
// This stub instantiates a behavioral synchronizer for backward compatibility
// in simulation and synthesis flows that have not yet switched to tech_cells_generic.
// For proper cell-library integration use the tech_cells_generic version.

module cc_sync #(
    parameter int unsigned Stages = 2,
    parameter bit ResetValue = 1'b0
) (
    input  logic clk_i,
    input  logic rst_ni,
    input  logic serial_i,
    output logic serial_o
);
  // synthesis translate_off
  initial $warning("Module 'cc_sync' has moved to 'tech_cells_generic'. Update your dependency.");
  // synthesis translate_on
  logic [Stages-1:0] serial_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      serial_q <= {Stages{ResetValue}};
    end else begin
      serial_q <= {serial_q[Stages-2:0], serial_i};
    end
  end
  assign serial_o = serial_q[Stages-1];
endmodule

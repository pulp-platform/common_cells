// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated

module serial_deglitch #(
  parameter int unsigned SIZE = 4
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic en_i,
  input  logic d_i,
  output logic q_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated.");
  // synthesis translate_on

  logic [SIZE-1:0] count_q;
  logic q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      count_q <= '0;
      q       <= 1'b0;
    end else begin
      if (en_i) begin
        if (d_i == 1'b1 && count_q != SIZE[SIZE-1:0]) begin
          count_q <= count_q + 1;
        end else if (d_i == 1'b0 && count_q != SIZE[SIZE-1:0]) begin
          count_q <= count_q - 1;
        end
      end
    end
  end

  // output process
  always_comb begin
    if (count_q == SIZE[SIZE-1:0]) begin
      q_o = 1'b1;
    end else if (count_q == 0) begin
      q_o = 1'b0;
    end
  end
endmodule

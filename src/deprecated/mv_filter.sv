// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated
module mv_filter #(
    parameter int unsigned WIDTH     = 4,
    parameter int unsigned THRESHOLD = 10
)(
    input  logic clk_i,
    input  logic rst_ni,
    input  logic sample_i,
    input  logic clear_i,
    input  logic d_i,
    output logic q_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated.");
  // synthesis translate_on

    logic [WIDTH-1:0] counter_q, counter_d;
    logic d, q;

    assign q_o = q;

    always_comb begin
        counter_d = counter_q;
        d = q;

        if (counter_q >= THRESHOLD[WIDTH-1:0]) begin
            d = 1'b1;
        end else if (sample_i && d_i) begin
            counter_d = counter_q + 1;
        end

        // sync reset
        if (clear_i) begin
            counter_d = '0;
            d = 1'b0;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            counter_q <= '0;
            q         <= 1'b0;
        end else begin
            counter_q <= counter_d;
            q         <= d;
        end
    end
endmodule

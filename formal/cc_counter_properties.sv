// Copyright 2019-2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Robert Balas <balasr@iis.ee.ethz.ch>
//
// Public-interface reference model for cc_counter and cc_delta_counter.
//
// The checker deliberately does not bind to the implementation state.  The
// WIDTH+1 reference counter is the observable state represented by q_o and the
// transient overflow flag; sticky overflow is tracked independently.
module cc_counter_properties #(
    parameter int unsigned WIDTH           = 4,
    parameter bit          STICKY_OVERFLOW = 1'b0,
    // Cover targets shared by the elaboration harness are enabled on one
    // representative instance to avoid duplicating identical obligations.
    parameter bit          CHECK_COMMON_COVERS = 1'b0,
    parameter bit          CHECK_ARITHMETIC_COVERS = 1'b0,
    parameter bit          CHECK_RESET_COVERS = 1'b0
) (
    input logic             clk_i,
    input logic             rst_ni,
    input logic             clr_i,
    input logic             en_i,
    input logic             load_i,
    input logic             down_i,
    input logic [WIDTH-1:0] delta_i,
    input logic [WIDTH-1:0] d_i,
    input logic [WIDTH-1:0] q_o,
    input logic             overflow_o
);

    logic [WIDTH:0] model_counter_q;
    logic [WIDTH:0] model_counter_d;
    logic           model_overflow_q;
    logic           model_overflow_d;

    // Require reset to be exercised at the beginning, while allowing reset to
    // be asserted and released again at any later point in a trace.
    logic init = 1'b0;
    logic reset_released_q = 1'b0;
    always_ff @(posedge clk_i) begin
        if (!init) begin
            assume (!rst_ni);
        end
        init <= 1'b1;
        if (rst_ni)
            reset_released_q <= 1'b1;
    end

    // This is the priority implemented by cc_delta_counter's two FFARNCs:
    // asynchronous reset, synchronous clear, then load, then count/hold.
    always_comb begin
        model_counter_d = model_counter_q;
        if (clr_i) begin
            model_counter_d = '0;
        end else if (load_i) begin
            model_counter_d = {1'b0, d_i};
        end else if (en_i) begin
            if (down_i) begin
                model_counter_d = model_counter_q - {1'b0, delta_i};
            end else begin
                model_counter_d = model_counter_q + {1'b0, delta_i};
            end
        end

        model_overflow_d = model_overflow_q;
        if (clr_i || load_i) begin
            model_overflow_d = 1'b0;
        end else if (en_i && !model_overflow_q) begin
            // Sticky overflow uses the low WIDTH bits, exactly as the DUT.
            if (down_i) begin
                model_overflow_d = delta_i > model_counter_q[WIDTH-1:0];
            end else begin
                model_overflow_d = model_counter_q[WIDTH-1:0] >
                                   ({WIDTH{1'b1}} - delta_i);
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            model_counter_q <= '0;
            model_overflow_q <= 1'b0;
        end else begin
            model_counter_q <= model_counter_d;
            model_overflow_q <= model_overflow_d;
        end
    end

    // Immediate assertions are used here because the Slang/Yosys frontend
    // intentionally does not lower concurrent SVA.  At a clock edge these
    // checks observe the state from the preceding edge, before either the DUT
    // or the reference model takes its nonblocking update.
    always @(posedge clk_i) begin
        // Asynchronous reset is part of the public contract and is checked at
        // the clock edge as well as through the reference model after release.
        if (!rst_ni) begin
            assert (q_o == '0);
            assert (overflow_o == 1'b0);
        end else begin
            // The q output is the low WIDTH bits of the full counter state.
            assert (q_o == model_counter_q[WIDTH-1:0]);

            if (STICKY_OVERFLOW) begin
                assert (overflow_o == model_overflow_q);
            end else begin
                // In transient mode overflow is the extra bit of the
                // WIDTH+1 counter.
                assert (overflow_o == model_counter_q[WIDTH]);
            end

            // The covers use only public inputs and outputs.  The arithmetic
            // predicates identify a real up-overflow or down-underflow event,
            // while the separate flag cover requires the resulting output to
            // be observable in a trace.
            if (CHECK_COMMON_COVERS) begin
                cover (clr_i);
                cover (load_i);
            end
            cover (overflow_o);
            if (CHECK_ARITHMETIC_COVERS) begin
                cover (en_i && !down_i && !clr_i && !load_i &&
                       (q_o > ({WIDTH{1'b1}} - delta_i)));
                cover (en_i && down_i && !clr_i && !load_i && (q_o < delta_i));
            end
        end
    end

    // Reset release and a later reset assertion each have a direct bounded
    // cover target.  The initial reset assumption only constrains the first
    // edge; no assumption prevents subsequent reset activity.
    if (CHECK_RESET_COVERS) begin : gen_reset_covers
        always @(posedge clk_i) begin
            cover (init && rst_ni);
            cover (reset_released_q && !rst_ni);
        end
    end

endmodule : cc_counter_properties

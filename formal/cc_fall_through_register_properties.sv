// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software and hardware distributed under this
// License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Public-interface checker for the fall-through register.  The one-entry
// reference model intentionally does not inspect the cc_fifo used by the
// implementation.
module cc_fall_through_register_properties #(
    parameter int unsigned DataWidth = 1,
    parameter type         data_t    = logic [DataWidth-1:0],
    parameter bit          CheckResetReleaseCover = 1'b0
) (
    input logic                 clk_i,
    input logic                 rst_ni,
    input logic                 clr_i,
    input logic                 valid_i,
    input logic                 ready_o,
    input data_t                data_i,
    input logic                 valid_o,
    input logic                 ready_i,
    input data_t                data_o
);

    logic stored_q;
    data_t stored_data_q;
    logic source_stall_q;
    data_t source_data_q;
    logic output_stall_q;
    data_t output_data_q;

    // The first cycle is reset.  Reset may be asserted again later and is
    // handled by the reference state below.
    logic init_q = 1'b0;

    logic rst_prev_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)
            rst_prev_q <= 1'b0;
        else
            rst_prev_q <= 1'b1;
    end

    // Reference state for the one-entry queue.  A valid/ready transfer while
    // empty is bypassed combinationally; a valid input held while ready_i is
    // low is captured at the next edge.
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            stored_q      <= 1'b0;
            stored_data_q <= '0;
        end else if (clr_i) begin
            stored_q      <= 1'b0;
            stored_data_q <= '0;
        end else if (stored_q) begin
            if (ready_i)
                stored_q <= 1'b0;
        end else if (valid_i && !ready_i) begin
            stored_q      <= 1'b1;
            stored_data_q <= data_i;
        end
    end

    // Immediate checks are used because the Slang/Yosys frontend does not
    // lower concurrent SVA.  The model and DUT are sampled before their
    // nonblocking updates at each edge.
    always @(posedge clk_i) begin
        if (!init_q)
            assume (!rst_ni);
        init_q <= 1'b1;

        if (rst_ni) begin
            // A source holds data while it was stalled during the previous
            // cycle.  A synchronous clear releases that obligation.
            if (source_stall_q && !clr_i)
                assume (valid_i && (data_i == source_data_q));

            assert (ready_o == !stored_q);
            assert (valid_o == (stored_q || valid_i));
            if (valid_o) begin
                if (stored_q)
                    assert (data_o == stored_data_q);
                else
                    assert (data_o == data_i);
            end

            // Output data remains stable during a stall until a transfer is
            // accepted.  A clear at the current edge is allowed to release
            // the item, so no post-clear valid assertion is made here.
            if (output_stall_q)
                assert (valid_o && (data_o == output_data_q));

            if (CheckResetReleaseCover)
                cover (!rst_prev_q && rst_ni);
            cover (!stored_q && valid_i && ready_i && valid_o &&
                   (data_i == data_o));
            cover (source_stall_q);
            cover (source_stall_q && clr_i);
            cover (output_stall_q && valid_o && ready_i);
            cover (clr_i && stored_q);
        end

        if (!rst_ni) begin
            source_stall_q <= 1'b0;
            output_stall_q <= 1'b0;
        end else begin
            source_stall_q <= valid_i && !ready_o && !clr_i;
            if (valid_i && !ready_o)
                source_data_q <= data_i;
            output_stall_q <= valid_o && !ready_i && !clr_i;
            if (valid_o && !ready_i)
                output_data_q <= data_o;
        end
    end

endmodule : cc_fall_through_register_properties

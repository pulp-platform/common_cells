// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Public-interface FIFO checker.  This checker deliberately models the FIFO
// from its stream interface only.  In particular, it does not rely on the
// implementation's pointers, counter, or memory, so it also applies to
// alternative implementations of the same interface.
module cc_fifo_properties import cc_pkg::*; #(
    parameter bit          FallThrough = 1'b0,
    parameter int unsigned DataWidth   = 2,
    parameter int unsigned Depth       = 1,
    parameter type         data_t      = logic [DataWidth-1:0],
    parameter bit          CheckUsage  = 1'b1,
    parameter bit          CheckResetReleaseCover = 1'b0,
    localparam int unsigned UsageWidth  = cc_pkg::cnt_width(Depth),
    localparam int unsigned PtrWidth    = cc_pkg::idx_width(Depth),
    localparam int unsigned FifoDepth   = (Depth > 0) ? Depth : 1
) (
    input logic                  clk_i,
    input logic                  rst_ni,
    input logic                  clr_i,
    input logic                  flush_i,
    input logic                  full_o,
    input logic                  empty_o,
    input logic [UsageWidth-1:0] usage_o,
    input data_t                 data_i,
    input logic                  push_i,
    input data_t                 data_o,
    input logic                  pop_i
);

    logic [UsageWidth-1:0] model_count_q;
    logic [PtrWidth-1:0]   model_read_q, model_write_q;
    data_t                 model_mem_q [FifoDepth];

    localparam logic [UsageWidth-1:0] DepthValue = Depth;
    localparam logic [PtrWidth-1:0]   LastPointer = FifoDepth - 1;

    logic bypass;
    logic bypass_transfer;
    logic stored_push;
    logic stored_pop;
    logic flush_prev_nonempty_q;
    logic clr_prev_nonempty_q;

    assign bypass = FallThrough && (model_count_q == '0) && push_i;
    assign bypass_transfer = bypass && pop_i;
    // An empty fall-through push is stored when it is not consumed in the
    // same cycle.  Only the simultaneous push/pop case is a pure bypass.
    assign stored_push = push_i && !clr_i && !flush_i &&
                         (model_count_q != DepthValue) && !bypass_transfer;
    assign stored_pop  = pop_i && !clr_i && !flush_i && (model_count_q != '0);

    function automatic logic [PtrWidth-1:0] pointer_inc(
        input logic [PtrWidth-1:0] pointer
    );
        if (pointer == LastPointer)
            pointer_inc = '0;
        else
            pointer_inc = pointer + 1'b1;
    endfunction

    // The first cycle is reset.  This constrains only the initial state;
    // reset can be asserted again at any later time.
    logic init_q = 1'b0;

    logic rst_prev_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)
            rst_prev_q <= 1'b0;
        else
            rst_prev_q <= 1'b1;
    end

    // Reference state.  clr_i clears both state and payload storage, while
    // flush_i clears only the queue pointers/count, matching cc_fifo.
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            model_count_q <= '0;
            model_read_q  <= '0;
            model_write_q <= '0;
            for (int unsigned i = 0; i < FifoDepth; i++)
                model_mem_q[i] <= '0;
        end else if (clr_i || flush_i) begin
            model_count_q <= '0;
            model_read_q  <= '0;
            model_write_q <= '0;
            if (clr_i) begin
                for (int unsigned i = 0; i < FifoDepth; i++)
                    model_mem_q[i] <= '0;
            end
        end else begin
            if (stored_push) begin
                model_mem_q[model_write_q] <= data_i;
                model_write_q <= pointer_inc(model_write_q);
            end
            if (stored_pop)
                model_read_q <= pointer_inc(model_read_q);

            case ({stored_push, stored_pop})
                2'b10: model_count_q <= model_count_q + 1'b1;
                2'b01: model_count_q <= model_count_q - 1'b1;
                default: model_count_q <= model_count_q;
            endcase
        end
    end

    // Immediate checks are used because the Slang/Yosys frontend does not
    // lower concurrent SVA.  At a clock edge both the DUT and this model are
    // sampled before their nonblocking updates, so the checks compare the
    // same queue state.
    always @(posedge clk_i) begin
        if (!init_q)
            assume (!rst_ni);
        init_q <= 1'b1;

        if (rst_ni) begin
            // Interface legality is derived from the independent model, not
            // from DUT status outputs.  A full model may not accept a push;
            // an empty model may not accept a pop except for the legal
            // fall-through empty push/pop bypass transaction.
            assume (!(model_count_q == DepthValue && push_i));
            assume (!(model_count_q == '0 && pop_i && !bypass));

            if (CheckUsage)
                assert (usage_o == model_count_q);
            assert (full_o == (model_count_q == DepthValue));
            assert (empty_o == ((model_count_q == '0) && !bypass));

            if (bypass)
                assert (data_o == data_i);
            else if (model_count_q != '0)
                assert (data_o == model_mem_q[model_read_q]);

            // Bounded cover targets: reset release, full, pointer wrap,
            // flush, simultaneous transfer, and fall-through bypass.
            if (CheckResetReleaseCover)
                cover (!rst_prev_q && rst_ni);
            cover (full_o);
            cover (stored_push && (model_write_q == LastPointer));
            cover (flush_prev_nonempty_q && empty_o);
            cover (clr_prev_nonempty_q && empty_o);
            if (Depth > 1)
                cover (push_i && pop_i && (model_count_q != '0) &&
                       !full_o && !empty_o);
            if (FallThrough)
                cover (bypass_transfer && (data_o == data_i));
        end

        if (!rst_ni) begin
            flush_prev_nonempty_q <= 1'b0;
            clr_prev_nonempty_q <= 1'b0;
        end else begin
            // Exercise clear and flush independently; a combined pulse would
            // otherwise satisfy both cover obligations with one trace.
            flush_prev_nonempty_q <= flush_i && !clr_i && (model_count_q != '0);
            clr_prev_nonempty_q <= clr_i && !flush_i && (model_count_q != '0);
        end
    end

endmodule : cc_fifo_properties

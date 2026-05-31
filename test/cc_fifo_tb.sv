// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Testbench for generic FIFO
module cc_fifo_inst_tb #(
    // FIFO parameters
    parameter bit          FallThrough,
    parameter int unsigned Depth,
    parameter int unsigned DataWidth = 8,
    // TB parameters
    parameter int unsigned NumChecks,
    parameter time         Ta,
    parameter time         Tt
) (
    input  logic    clk_i,
    input  logic    rst_ni,
    output logic    done_o
);

    import rand_verif_pkg::rand_wait;

    typedef logic [DataWidth-1:0] data_t;

    logic           clk,
                    flush,
                    full,
                    empty,
                    push,
                    pop,
                    try_push,
                    try_pop;

    data_t          wdata,
                    rdata;

    int unsigned    n_checks = 0;

    assign clk = clk_i;

    cc_fifo #(
        .FallThrough    ( FallThrough   ),
        .DataWidth      ( DataWidth     ),
        .Depth          ( Depth         )
    ) dut (
        .clk_i,
        .rst_ni,
        .flush_i        ( flush         ),
        .full_o         ( full          ),
        .empty_o        ( empty         ),
        .usage_o        (               ),
        .data_i         ( wdata         ),
        .push_i         ( push          ),
        .data_o         ( rdata         ),
        .pop_i          ( pop           )
    );

    // Simulation information and stopping.
    // TODO: Better stop after certain coverage is reached.
    initial begin
        done_o = 1'b0;
        $display("%m: Running test with FallThrough=%0d, Depth=%0d", FallThrough, Depth);
        wait (n_checks >= NumChecks);
        done_o = 1'b1;
        $display("%m: Checked %0d stimuli", n_checks);
    end

    class random_action_t;
        rand logic [1:0] action;
        constraint random_action {
            action dist {
                0 := 40,
                1 := 40,
                3 := 2,
                0 := 0
            };
        }
    endclass

    // Input driver: push, wdata, and flush
    assign push = try_push & ~full;
    initial begin
        automatic random_action_t rand_act = new();
        flush       <= 1'b0;
        wdata       <= 'x;
        try_push    <= 1'b0;
        wait (rst_ni);
        forever begin
            static logic rand_success;
            rand_wait(1, 8, clk);
            rand_success = rand_act.randomize(); assert(rand_success);
            case (rand_act.action)
                0: begin // new random data and try to push
                    wdata       <= #Ta $random();
                    try_push    <= #Ta 1'b1;
                end
                1: begin // new random data but do not try to push
                    wdata       <= #Ta $random();
                    try_push    <= #Ta 1'b0;
                end
                2: begin // flush
                    flush       <= #Ta 1'b1;
                    rand_wait(1, 8, clk);
                    flush       <= #Ta 1'b0;
                end
            endcase
        end
    end

    // Output driver: pop
    assign pop = try_pop & ~empty;
    initial begin
        try_pop <= 1'b0;
        wait (rst_ni);
        forever begin
            rand_wait(1, 8, clk);
            try_pop <= #Ta $random();
        end
    end

    // Monitor & checker: model expected response and check against actual response
    initial begin
        data_t queue[$];
        wait (rst_ni);
        forever begin
            @(posedge clk_i);
            #(Tt);
            if (flush) begin
                queue = {};
            end else begin
                if (push && !full) begin
                    queue.push_back(wdata);
                end
                if (pop && !empty) begin
                    automatic data_t data = queue.pop_front();
                    assert (rdata == data) else $error("Queue output %0x != %0x", rdata, data);
                    n_checks++;
                end
            end
        end
    end

// https://github.com/verilator/verilator/issues/5981
`ifndef VERILATOR
    if (FallThrough) begin
        // In fall through mode, assert that the output data is equal to the input data when pushing
        // to an empty FIFO.
        assert property (@(posedge clk_i) ((empty & ~push) ##1 push) |-> rdata == wdata)
            else $error("Input did not fall through");
    end
`endif

endmodule

// Testbench for different FIFO configurations
module cc_fifo_tb #(
    // TB parameters
    parameter int unsigned NumChecks = 100000,
    parameter time         Tclk      = 10ns,
    parameter time         Ta        = Tclk * 1/4,
    parameter time         Tt        = Tclk * 3/4
);

    logic       clk,
                rst_n;

    logic [5:0] done;

    clk_rst_gen #(.ClkPeriod(Tclk), .RstClkCycles(10)) i_clk_rst_gen (
        .clk_o    (clk),
        .rst_no   (rst_n)
    );

    cc_fifo_inst_tb #(
        .FallThrough(1'b0),
        .Depth      (8),
        .NumChecks  (NumChecks),
        .Ta         (Ta),
        .Tt         (Tt)
    ) i_tb_8 (
        .clk_i (clk),
        .rst_ni(rst_n),
        .done_o(done[0])
    );

    cc_fifo_inst_tb #(
        .FallThrough(1'b1),
        .Depth      (8),
        .NumChecks  (NumChecks),
        .Ta         (Ta),
        .Tt         (Tt)
    ) i_tb_ft_8 (
        .clk_i (clk),
        .rst_ni(rst_n),
        .done_o(done[1])
    );

    cc_fifo_inst_tb #(
        .FallThrough(1'b0),
        .Depth      (1),
        .NumChecks  (NumChecks),
        .Ta         (Ta),
        .Tt         (Tt)
    ) i_tb_1 (
        .clk_i (clk),
        .rst_ni(rst_n),
        .done_o(done[2])
    );

    cc_fifo_inst_tb #(
        .FallThrough(1'b1),
        .Depth      (1),
        .NumChecks  (NumChecks),
        .Ta         (Ta),
        .Tt         (Tt)
    ) i_tb_ft_1 (
        .clk_i (clk),
        .rst_ni(rst_n),
        .done_o(done[3])
    );

    cc_fifo_inst_tb #(
        .FallThrough(1'b0),
        .Depth      (9),
        .NumChecks  (NumChecks),
        .Ta         (Ta),
        .Tt         (Tt)
    ) i_tb_9 (
        .clk_i (clk),
        .rst_ni(rst_n),
        .done_o(done[4])
    );

    cc_fifo_inst_tb #(
        .FallThrough(1'b1),
        .Depth      (9),
        .NumChecks  (NumChecks),
        .Ta         (Ta),
        .Tt         (Tt)
    ) i_tb_ft_9 (
        .clk_i (clk),
        .rst_ni(rst_n),
        .done_o(done[5])
    );

    initial begin
        wait ((&done));
        $finish();
    end

endmodule

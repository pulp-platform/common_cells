// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

import rand_verif_pkg::rand_wait;

// Testbench for generic FIFO
module fifo_tb #(
    // FIFO parameters
    parameter bit           FALL_THROUGH    = 1'b1,
    parameter int unsigned  DATA_WIDTH      = 8,
    parameter int unsigned  DEPTH           = 8,
    parameter int unsigned  ALM_FULL_TH     = 6,
    parameter int unsigned  ALM_EMPTY_TH    = 2,
    // TB parameters
    parameter int unsigned  N_CHECKS        = 100000,
    parameter time          TCLK            = 10ns,
    parameter time          TA              = TCLK * 1/4,
    parameter time          TT              = TCLK * 3/4
);

    timeunit 1ns;
    timeprecision 10ps;

    typedef logic [DATA_WIDTH-1:0] data_t;

    logic           clk,
                    rst_n,
                    flush,
                    full,
                    empty,
                    alm_full,
                    alm_empty,
                    push,
                    pop,
                    try_push,
                    try_pop;

    data_t          wdata,
                    rdata;

    int unsigned    n_checks = 0;

    fifo_v2 #(
        .FALL_THROUGH   ( FALL_THROUGH  ),
        .DATA_WIDTH     ( DATA_WIDTH    ),
        .DEPTH          ( DEPTH         ),
        .ALM_FULL_TH    ( ALM_FULL_TH   ),
        .ALM_EMPTY_TH   ( ALM_EMPTY_TH  )
    ) dut (
        .clk_i          ( clk           ),
        .rst_ni         ( rst_n         ),
        .testmode_i     ( 1'b0          ),
        .flush_i        ( flush         ),
        .full_o         ( full          ),
        .empty_o        ( empty         ),
        .alm_full_o     ( alm_full      ),
        .alm_empty_o    ( alm_empty     ),
        .data_i         ( wdata         ),
        .push_i         ( push          ),
        .data_o         ( rdata         ),
        .pop_i          ( pop           )
    );

    clk_rst_gen #(.CLK_PERIOD(TCLK), .RST_CLK_CYCLES(10)) i_clk_rst_gen (
        .clk_o    (clk),
        .rst_no   (rst_n)
    );

    // Simulation information and stopping.
    // TODO: Better stop after certain coverage is reached.
    initial begin
        $display("Running test with FALL_THROUGH=%0d, DEPTH=%0d", FALL_THROUGH, DEPTH);
        wait (n_checks >= N_CHECKS);
        $display("Checked %0d stimuli", n_checks);
        $stop;
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
        wait (rst_n);
        forever begin
            static logic rand_success;
            rand_wait(1, 8, clk);
            rand_success = rand_act.randomize(); assert(rand_success);
            case (rand_act.action)
                0: begin // new random data and try to push
                    wdata       <= #TA $random();
                    try_push    <= #TA 1'b1;
                end
                1: begin // new random data but do not try to push
                    wdata       <= #TA $random();
                    try_push    <= #TA 1'b0;
                end
                2: begin // flush
                    flush       <= #TA 1'b1;
                    rand_wait(1, 8, clk);
                    flush       <= #TA 1'b0;
                end
            endcase
        end
    end

    // Output driver: pop
    assign pop = try_pop & ~empty;
    initial begin
        try_pop <= 1'b0;
        wait (rst_n);
        forever begin
            rand_wait(1, 8, clk);
            try_pop <= #TA $random();
        end
    end

    // Monitor & checker: model expected response and check against actual response
    initial begin
        data_t queue[$];
        wait (rst_n);
        forever begin
            @(posedge clk);
            #(TT);
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

endmodule

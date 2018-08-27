// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zaruabf@iis.ee.ethz.ch>

/// Testbench for generic FIFO
module fifo_tb #(
    parameter bit          FALL_THROUGH  = 1'b1,
    parameter int unsigned DEPTH         = 8,
    parameter int unsigned ALM_FULL_TH   = 6,
    parameter int unsigned ALM_EMPTY_TH  = 2
);

    logic clk, rst_n;

    logic flush, full, empty, alm_full, alm_empty, push, pop;

    logic [7:0] wdata, rdata;

    int unsigned nr_checks;

    fifo_v2 #(
        .FALL_THROUGH ( FALL_THROUGH ),
        .DATA_WIDTH   ( 8            ),
        .DEPTH        ( DEPTH        ),
        .ALM_FULL_TH  ( ALM_FULL_TH  ),
        .ALM_EMPTY_TH ( ALM_EMPTY_TH )
    ) dut (
        .clk_i        ( clk       ),
        .rst_ni       ( rst_n     ),
        .testmode_i   ( 1'b0      ),
        .flush_i      ( flush     ),
        .full_o       ( full      ),
        .empty_o      ( empty     ),
        .alm_full_o   ( alm_full  ),
        .alm_empty_o  ( alm_empty ),
        .data_i       ( wdata     ),
        .push_i       ( push      ),
        .data_o       ( rdata     ),
        .pop_i        ( pop       )
    );

    initial begin
        clk = 1'b0;
        rst_n = 1'b0;
        repeat(8)
            #10ns clk = ~clk;

        rst_n = 1'b1;
        forever
            #10ns clk = ~clk;
    end

    // simulator stopper, this is suboptimal better go for coverage
    initial begin
        #100ms
        $display("Checked %d stimuli", nr_checks);
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

    program testbench ();
        logic[7:0] queue [$];
        // clocking outputs are DUT inputs and vice versa
        clocking cb @(posedge clk);
            default input #2 output #4;
            output flush, wdata, push, pop;
            input full, empty, rdata, alm_full, alm_empty;
        endclocking

        clocking pck @(posedge clk);
            default input #2 output #4;
            input flush, wdata, push, pop, full, empty, rdata, alm_full, alm_empty;
        endclocking

        initial begin
            $display("Running test with parameter:\nFALL_THROUGH: %d\nDEPTH: %d", FALL_THROUGH, DEPTH);
        end
        // --------
        // Driver
        // --------
        initial begin
            automatic random_action_t random_action = new();

            cb.flush <= 1'b0;

            wait (rst_n == 1'b1);
            push  <= 1'b0;

            forever begin
                void'(random_action.randomize());
                repeat($urandom_range(0, 8)) @(cb);
                // $display("%d\n", random_action.action);
                if (random_action.action == 0) begin
                    cb.wdata <= $urandom_range(0,256);
                    cb.push  <= 1'b1;
                end else if (random_action.action == 1) begin
                    cb.flush <= 1'b0;
                    cb.wdata <= $urandom_range(0,256);
                    cb.push  <= 1'b0;
                end else begin
                    cb.flush <= 1'b1;
                    cb.push  <= 1'b0;
                    @(cb);
                    cb.flush <= 1'b0;
                end
            end
        end

        initial begin
            // wait for reset to be high
            wait (rst_n == 1'b1);
            // pop from queue
            forever begin
                @(cb)
                cb.pop <= 1'b1;
                repeat($urandom_range(0, 8)) @(cb);
                cb.pop <= 1'b0;
            end
        end

        // -------------------
        // Monitor && Checker
        // -------------------
        initial begin
            automatic logic [7:0] data;
            nr_checks = 0;
            forever begin
                @(pck)

                if (pck.push && !pck.full && !pck.flush) begin
                    queue.push_back(pck.wdata);
                end

                if (pck.pop && !pck.empty) begin
                    data = queue.pop_front();
                    // $display("Time: %t, Expected: %0h Got %0h", $time, data, fifo_if.pck.rdata);
                    assert(data == pck.rdata) else $error("Mismatch, Expected: %0h Got %0h", data, pck.rdata);
                    nr_checks++;
                end

                if (pck.flush) begin
                    queue = {};
                end

            end
        end
    endprogram

    testbench tb();
endmodule

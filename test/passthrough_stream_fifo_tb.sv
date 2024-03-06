// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Authors:
// - Tobias Senti <tsenti@ethz.ch>

`timescale 1ns/1ns

/// This modules verifies basic operation of the passthrough_stream_fifo_tb.
module passthrough_stream_fifo_tb #(
    parameter int unsigned TCK              = 10,
    parameter int unsigned DataWidth        = 8,
    parameter int unsigned Depth            = 10,
    parameter int unsigned NumStims         = 1000,
    parameter int unsigned WriteProbability = 10,
    parameter int unsigned ReadProbability  = 10,
    parameter bit          SameCycleRW      = 1'b1
) ();
    typedef logic [DataWidth-1:0] data_t;

    int unsigned applied_stims, acquired_stims;

    logic clk, rst_n;

    data_t in_data, out_data;
    logic in_valid, in_ready, out_valid, out_ready;    

    // Data queues
    data_t app_queue[$], acq_queue[$];

    //Clock generator
    clk_rst_gen #(
        .ClkPeriod    ( TCK  ),
        .RstClkCycles ( 1     )
    ) i_clk_rst_gen (
        .clk_o        ( clk   ),
        .rst_no       ( rst_n )
    );

    // DUT
    passthrough_stream_fifo #(
        .Depth       ( Depth       ),
        .type_t      ( data_t      ),
        .PrintInfo   ( 1'b1        ),
        .SameCycleRW ( SameCycleRW )
    ) i_passthrough_stream_fifo (
        .clk_i      ( clk ),
        .rst_ni     ( rst_n ),
        .flush_i    ( 1'b0 ),
        .testmode_i ( 1'b0 ),

        .data_i  ( (in_valid && in_ready) ? in_data : 'x ),
        .valid_i ( in_valid && in_ready                  ),
        .ready_o ( in_ready                              ),

        .data_o  ( out_data               ),
        .valid_o ( out_valid              ),
        .ready_i ( out_ready && out_valid )
    );

    // Application
    initial begin
        applied_stims = 0;
        in_data       = '0;
        in_valid      = 1'b0;

        // Wait for reset
        wait(rst_n);

        $display("Started application!");

        while(applied_stims < NumStims) begin
            @(negedge clk);
            in_valid = $urandom_range(0, WriteProbability) == 0;
            in_data = $urandom();
            @(posedge clk); 
            if (in_valid && in_ready) begin
                $display("%d Applied: %d", applied_stims, in_data);
                app_queue.push_back(in_data);
                applied_stims++;
            end
        end
        in_valid = 1'b0;

        $display("Applied %d stimuli", applied_stims);
    end

    // Acquisition
    initial begin
        acquired_stims = 0;
        out_ready = 1'b0;

        // Wait for reset
        wait(rst_n);

        $display("Started acquisition!");

        forever begin
            @(negedge clk);
            out_ready = $urandom_range(0, ReadProbability) == 0;
            @(posedge clk);
            if (out_valid && out_ready) begin
                $display("%d Acquired: %d", acquired_stims, out_data);
                acq_queue.push_back(out_data);
                acquired_stims++;
            end 
        end
    end

    // Response Checking
    initial begin
        int unsigned num_errors;
        data_t acq_data, app_data;

        num_errors = 0;

        while((acquired_stims < NumStims) || (applied_stims < NumStims)) begin
            wait((app_queue.size() != 0) && (acq_queue.size() != 0));

            acq_data = acq_queue.pop_front();
            app_data = app_queue.pop_front();

            if (app_data != acq_data) begin
                $display("Missmatch! Applied: %d Acquired: %d", app_data, acq_data);
                num_errors++;
            end else begin
                $display("Match! Applied: %d Acquired: %d", app_data, acq_data);
            end
        end
        $display("Applied %d stimuli and acquired %d responses", applied_stims, acquired_stims);
        $display("Errors: %d", num_errors);
        $stop();
    end
endmodule

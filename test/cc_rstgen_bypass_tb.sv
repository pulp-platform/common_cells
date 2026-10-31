// Copyright 2026 common_cells contributors.
// SPDX-License-Identifier: SHL-0.51

module cc_rstgen_bypass_tb #(
    parameter int NumRegs = 4
);
    timeunit 1ns;
    timeprecision 1ps;

    logic clk = 0;
    logic rst_n = 1;
    logic test_rst_n = 1;
    logic test_mode = 0;
    logic rst_out_n, init_out_n;

    cc_rstgen_bypass #(.NumRegs(NumRegs)) dut (
        .clk_i(clk),
        .rst_ni(rst_n),
        .rst_test_mode_ni(test_rst_n),
        .test_mode_i(test_mode),
        .rst_no(rst_out_n),
        .init_no(init_out_n)
    );

    task automatic check_outputs(input logic expected_rst, input logic expected_init);
        #1;
        if (rst_out_n !== expected_rst || init_out_n !== expected_init) begin
            $fatal(1, "NumRegs=%0d: expected rst/init=%b/%b, got %b/%b",
                   NumRegs, expected_rst, expected_init, rst_out_n, init_out_n);
        end
    endtask

    task automatic check_release;
        // Releasing reset without a clock edge must not release the outputs.
        rst_n = 1;
        check_outputs(0, 0);
        for (int cycle = 1; cycle <= NumRegs + 1; cycle++) begin
            #4;
            clk = 1;
            check_outputs(cycle >= NumRegs, cycle >= NumRegs);
            #4;
            clk = 0;
        end
    endtask

    initial begin
        // Functional reset asserts asynchronously, including with a stopped clock.
        #2;
        rst_n = 0;
        check_outputs(0, 0);
        check_release;

        // Exercise a second reset after the synchronizer has filled with ones.
        #2;
        rst_n = 0;
        check_outputs(0, 0);
        check_release;

        // Select test mode while both resets are asserted. No clock is needed
        // for the test reset bypass; init_no stays high throughout test mode.
        rst_n = 0;
        test_rst_n = 0;
        check_outputs(0, 0);
        test_mode = 1;
        check_outputs(0, 1);
        test_rst_n = 1;
        check_outputs(1, 1);
        rst_n = 1;
        check_outputs(1, 1);
        rst_n = 0;
        check_outputs(1, 1);
        test_rst_n = 0;
        check_outputs(0, 1);

        // Return to functional mode with resets asserted, then resynchronize.
        test_mode = 0;
        check_outputs(0, 0);
        check_release;

        $display("PASS cc_rstgen_bypass NumRegs=%0d", NumRegs);
        $finish;
    end

    initial begin
        #10000;
        $fatal(1, "Timeout waiting for reset checks");
    end
endmodule

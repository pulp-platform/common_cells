module max_pow_two #(
    parameter int unsigned InpWidth       = 32,
    parameter int unsigned MaxPowTwoWidth = InpWidth
)(
    input  logic [InpWidth-1:0]       value_i,
    output logic [MaxPowTwoWidth-1:0] max_pow_two_o
);

    localparam int unsigned ShiftWidth = cf_math_pkg::idx_width(MaxPowTwoWidth);

    logic [ShiftWidth-1:0] shift;
    logic                  empty;

    lzc #(
        .WIDTH ( MaxPowTwoWidth  ),
        .MODE  ( 1'b1            )  // leading zero configuration
    ) i_lzc (
        .in_i    ( value_i[MaxPowTwoWidth-1:0] ),
        .cnt_o   ( shift                       ),
        .empty_o ( empty                       )
    );

    assign max_pow_two_o = empty ? '0 : (1'b1 << (MaxPowTwoWidth - 32'd1)) >> shift;

endmodule

module tb_max_pow_two #(
    parameter int unsigned InpWidth = 32,
    parameter int unsigned MaxPowTwoWidth = 16
);

    logic [InpWidth-1:0]       inp = 0;
    logic [MaxPowTwoWidth-1:0] oup;

    max_pow_two #(
        .InpWidth       ( InpWidth       ),
        .MaxPowTwoWidth ( MaxPowTwoWidth )
    ) i_max_pow_two (
        .value_i       ( inp      ),
        .max_pow_two_o ( oup      )
    );

    task apply_test (
        input logic [InpWidth-1:0] test
    );
        inp = test;
        #0;
        $display("Test: %d (0x%8h) [0b%b] -> %d (0x%8h) [0b%b]", test, test, test, oup, oup, oup);
        #10ns;
    endtask

    // test
    initial begin
        apply_test(0);
        apply_test(1);
        apply_test(2);
        apply_test(3);
        apply_test(4);
        apply_test(5);
        apply_test(8);
        apply_test(5694);
        apply_test(171717);
        apply_test(-2);
        apply_test(-1);
        $finish();
    end

endmodule

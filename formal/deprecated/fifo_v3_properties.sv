// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated adapter.  Keep this checker available for users of fifo_v3, but
// do not include it in the active proof targets.  The adapter sees only the
// fifo_v3 interface; it does not reach into fifo_v3's cc_fifo implementation.
module fifo_v3_properties #(
    parameter bit          FALL_THROUGH = 1'b0,
    parameter int unsigned DATA_WIDTH   = 32,
    parameter int unsigned DEPTH        = 8,
    parameter int unsigned PAYLOAD_WIDTH = DATA_WIDTH,
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
) (
    input logic                   clk_i,
    input logic                   rst_ni,
    input logic                   flush_i,
    input logic                   testmode_i,
    input logic                   full_o,
    input logic                   empty_o,
    input logic [ADDR_DEPTH-1:0]  usage_o,
    input logic [PAYLOAD_WIDTH-1:0] data_i,
    input logic                   push_i,
    input logic [PAYLOAD_WIDTH-1:0] data_o,
    input logic                   pop_i
);
    localparam int unsigned UsageWidth = cc_pkg::cnt_width(DEPTH);
    logic [UsageWidth-1:0] usage_full;

    // fifo_v3's legacy usage port is only ADDR_DEPTH bits wide and therefore
    // cannot represent the full count for power-of-two depths.  Preserve the
    // adapter's elaboration while checking all other public behavior.
    assign usage_full = usage_o;

    cc_fifo_properties #(
        .FallThrough ( FALL_THROUGH ),
        .DataWidth   ( PAYLOAD_WIDTH ),
        .Depth       ( DEPTH         ),
        .CheckUsage  ( 1'b0          )
    ) i_cc_fifo_properties (
        .clk_i   ( clk_i      ),
        .rst_ni  ( rst_ni     ),
        .clr_i   ( 1'b0       ),
        .flush_i ( flush_i    ),
        .full_o  ( full_o     ),
        .empty_o ( empty_o    ),
        .usage_o ( usage_full ),
        .data_i  ( data_i     ),
        .push_i  ( push_i     ),
        .data_o  ( data_o     ),
        .pop_i   ( pop_i      )
    );

    logic unused_testmode;
    assign unused_testmode = testmode_i;
endmodule : fifo_v3_properties

bind fifo_v3 fifo_v3_properties #(
    .FALL_THROUGH ( FALL_THROUGH ),
    .DATA_WIDTH   ( DATA_WIDTH   ),
    .DEPTH        ( DEPTH        ),
    .PAYLOAD_WIDTH( $bits(dtype) ),
    .ADDR_DEPTH   ( ADDR_DEPTH   )
) i_fifo_v3_properties (.*);

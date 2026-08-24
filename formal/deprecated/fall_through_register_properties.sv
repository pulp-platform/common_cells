// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated adapter.  This file is retained for legacy fall_through_register
// users and is intentionally excluded from the active proof targets.
module fall_through_register_properties #(
    parameter int unsigned DATA_WIDTH = 1
) (
    input logic                  clk_i,
    input logic                  rst_ni,
    input logic                  clr_i,
    input logic                  testmode_i,
    input logic                  valid_i,
    input logic                  ready_o,
    input logic [DATA_WIDTH-1:0] data_i,
    input logic                  valid_o,
    input logic                  ready_i,
    input logic [DATA_WIDTH-1:0] data_o
);
    cc_fall_through_register_properties #(
        .DataWidth ( DATA_WIDTH )
    ) i_cc_fall_through_register_properties (
        .clk_i   ( clk_i      ),
        .rst_ni  ( rst_ni     ),
        .clr_i   ( clr_i      ),
        .valid_i ( valid_i    ),
        .ready_o ( ready_o    ),
        .data_i  ( data_i     ),
        .valid_o ( valid_o    ),
        .ready_i ( ready_i    ),
        .data_o  ( data_o     )
    );

    logic unused_testmode;
    assign unused_testmode = testmode_i;
endmodule : fall_through_register_properties

// The legacy module exposes only its type parameter.  Binding the adapter
// with the packed width avoids forwarding the type parameter itself.
bind fall_through_register fall_through_register_properties #(
    .DATA_WIDTH ( $bits(T) )
) i_fall_through_register_properties (.*);

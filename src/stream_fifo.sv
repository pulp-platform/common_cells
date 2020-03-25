// give the fifo_v3 a rdy/vld interface so it can be inserted directly into streams

module stream_fifo #(
    parameter bit          FALL_THROUGH = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DATA_WIDTH   = 32,   // default data width if the fifo is of type logic
    parameter int unsigned DEPTH        = 8,    // depth can be arbitrary from 0 to 2**32
    parameter type dtype                = logic [DATA_WIDTH-1:0],
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
)(
    input logic                   clk_i,        // Clock
    input logic                   rst_ni,       // Asynchronous reset active low
    input logic                   flush_i,      // flush the queue
    input logic                   testmode_i,   // test_mode to bypass clock gating
    output logic [ADDR_DEPTH-1:0] usage_o,      // fill pointer
    // input interface
    input                         dtype data_i, // data to push into the queue
    input logic                   vld_i,        // input data valid
    output logic                  rdy_o,        // queue is not full
    // output interface
    output                        dtype data_o, // output data
    output logic                  vld_o,        // queue is not empty
    input logic                   rdy_i         // pop head from queue
);

  logic           push, pop;
  logic           empty, full;
  assign push = vld_i & ~full;
  assign pop = rdy_i & ~empty;
  assign rdy_o = ~full;
  assign vld_o = ~empty;

  fifo_v3 #(
            .FALL_THROUGH(FALL_THROUGH),
            .DATA_WIDTH(DATA_WIDTH),
            .DEPTH(DEPTH),
            .dtype(dtype)
            )
  fifo_i (
          .full_o(full),
          .empty_o(empty),
          .push_i(push),
          .pop_i(pop),
          .*
          );

endmodule // stream_fifo

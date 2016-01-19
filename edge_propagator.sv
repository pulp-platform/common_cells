////////////////////////////////////////////////////////////////////////////////
// Company:        Multitherman Laboratory @ DEIS - University of Bologna     //
//                    Viale Risorgimento 2 40136                              //
//                    Bologna - fax 0512093785 -                              //
//                                                                            //
// Engineer:       Antonio Pullini - pullinia@iis.ee.ethz.ch                  //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    13/02/2013                                                 //
// Design Name:    ULPSoC                                                     //
// Module Name:    edge_propagator                                            //
// Project Name:   ULPSoC                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    edge_propagator                                            //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (19/03/2015)   clock_gating swapped in pulp_clock_gating   //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module edge_propagator
(
    input logic clk_tx_i,
    input logic rstn_tx_i,
    input logic edge_i,
    input logic clk_rx_i,
    input logic rstn_rx_i,
    output logic edge_o
);

  reg [1:0] sync_a;
  wire      sync_b;

  reg  r_input_reg;
  wire s_input_reg_next;

  assign s_input_reg_next = edge_i | (r_input_reg & ~sync_a[0]);

  always @(negedge rstn_tx_i or posedge clk_tx_i)
  begin
    if (~rstn_tx_i)
    begin
      r_input_reg <= 1'b0;
      sync_a      <= 2'b00;
    end
    else
    begin
      r_input_reg <= s_input_reg_next;
      sync_a      <= {sync_b,sync_a[1]};
    end
  end

  pulp_sync_wedge u_sync_clkb(
            .clk_i(clk_rx_i), 
            .rstn_i(rstn_rx_i), 
            .en_i(1'b1), 
            .serial_i(r_input_reg), 
            .r_edge_i(edge_o), 
            .f_edge_i(), 
            .serial_o(sync_b));

endmodule









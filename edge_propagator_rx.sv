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


module edge_propagator_rx
(
    input  logic clk_i,
    input  logic rstn_i,
    input  logic valid_i,
    output logic ack_o,
    output logic valid_o
);

  sync_wedge u_sync_clkb(
            .clk(clk_i), 
            .rst_n(rstn_i), 
            .en(1'b1), 
            .serial_in(valid_i), 
            .rising_edge(valid_o), 
            .falling_edge(), 
            .serial_out(ack_o));

endmodule









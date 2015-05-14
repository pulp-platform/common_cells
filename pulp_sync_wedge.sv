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
// Module Name:    sync_wedge                                                 //
// Project Name:   ULPSoC                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    sync_wedge                                                 //
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

module pulp_sync_wedge
(
    input  logic clk_i,
    input  logic rstn_i,
    input  logic en_i,
    input  logic serial_i,
    output logic r_edge_o,
    output logic f_edge_o,
    output logic serial_o
);

  logic [2:0] r_reg;
  logic [2:0] r_next;

  always_ff @(posedge clk_i, negedge rstn_i)
  begin
    if(!rstn_i)
         r_reg <= 3'h0;
    else 
        if (en_i)
          r_reg <= {serial_i, r_reg[2:1]};
  end

  assign serial_o   =  r_reg[0];
  assign f_edge_o   = !r_reg[1] &  r_reg[0];
  assign r_edge_o   =  r_reg[1] & !r_reg[0];

endmodule


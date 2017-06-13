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

module pulp_sync
#(
    parameter STAGES = 2
)
(
    input  logic clk_i,
    input  logic rstn_i,
    input  logic serial_i,
    output logic serial_o
);

  logic [STAGES-1:0] r_reg;

  always_ff @(posedge clk_i, negedge rstn_i)
  begin
    if(!rstn_i)
         r_reg <= 'h0;
    else 
         r_reg <= {r_reg[STAGES-2:0], serial_i};
  end

  assign serial_o   =  r_reg[STAGES-1];

endmodule


////////////////////////////////////////////////////////////////////////////////
// Copyright (C) 2017 ETH Zurich, University of Bologna                       //
// All rights reserved.                                                       //
//                                                                            //
// This code is under development and not yet released to the public.         //
// Until it is released, the code is under the copyright of ETH Zurich and    //
// the University of Bologna, and may contain confidential and/or unpublished //
// work. Any reuse/redistribution is strictly forbidden without written       //
// permission from ETH Zurich.                                                //
//                                                                            //
// Bug fixes and contributions will eventually be released under the          //
// SolderPad open hardware license in the context of the PULP platform        //
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the  //
// University of Bologna.                                                     //
//                                                                            //
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

    pulp_sync_wedge  u_sync_clkb
    (
        .clk_i(clk_i), 
        .rstn_i(rstn_i), 
        .en_i(1'b1), 
        .serial_i(valid_i), 
        .r_edge_o(valid_o), 
        .f_edge_o(), 
        .serial_o(ack_o)
    );
/*    
    pulp_sync_wedge
    (
        input  logic clk_i,
        input  logic rstn_i,
        input  logic en_i,
        input  logic serial_i,
        output logic r_edge_o,
        output logic f_edge_o,
        output logic serial_o
    );*/

endmodule









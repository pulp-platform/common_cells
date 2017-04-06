/* Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * This code is under development and not yet released to the public.
 * Until it is released, the code is under the copyright of ETH Zurich and
 * the University of Bologna, and may contain confidential and/or unpublished 
 * work. Any reuse/redistribution is strictly forbidden without written
 * permission from ETH Zurich.
 *
 * Bug fixes and contributions will eventually be released under the
 * SolderPad open hardware license in the context of the PULP platform
 * (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
 * University of Bologna.
 */

// Available cells:
// LVT
// C12T28SOI_LLP_CNHLSX58_P0
// C12T28SOI_LLP_CNHLSX58_P4
// C12T28SOI_LLP_CNHLSX58_P10
// C12T28SOI_LLP_CNHLSX58_P16
// RVT
// C12T28SOI_LRP_CNHLSX58_P0
// C12T28SOI_LRP_CNHLSX58_P4
// C12T28SOI_LRP_CNHLSX58_P10
// C12T28SOI_LRP_CNHLSX58_P16
// UWVR
// C12T32_LLUAL4_CNHLSX7
//
// 8T RVT
// C8T28SOI_LRP_CNHLSX54_P0
// C8T28SOI_LRP_CNHLSX54_P4
// C8T28SOI_LRP_CNHLSX54_P10
// C8T28SOI_LRP_CNHLSX54_P16

`include "ulpsoc_defines.sv"

module pulp_clock_gating_async
(
   input  logic clk_i,
   input  logic rstn_i,
   input  logic en_async_i,
   input  logic test_en_i,
   output logic clk_o
);  

    logic     r_sync_0;
    logic     r_sync_1;
    
    always_ff(posedge clk_i or negedge rstn_i)
    begin
        if(~rstn_i)
	begin
            r_sync_0 <= 1'b1;
	    r_sync_1 <= 1'b1;
	end
        else
	begin
            r_sync_0 <= en_async_i;
	    r_sync_1 <= r_sync_0;
	end
    end
   
`ifdef CMOS28FDSOI_8T
   C8T28SOI_LRP_CNHLSX54_P0
     clk_gate_i (
		 .Q(clk_o),
		 .CP(clk_i),
		 .E(r_sync_1),
		 .TE(test_en_i)
		 );
`endif


`ifdef CMOS28FDSOI_12T_UWVR
   C12T32_LLUAL4_CNHLSX7
     clk_gate_i (
		 .Q(clk_o),
		 .CP(clk_i),
		 .E(r_sync_1),
		 .TE(test_en_i)
		 );
`endif   
   
endmodule

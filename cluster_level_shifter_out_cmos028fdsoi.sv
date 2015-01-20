// UWVR VOLTAGES ARE INVERTED: VDDI = VOUT, VDDO = VIN
// C12T32DG_LLU_LSINX26

`include "ulpsoc_defines.sv"

module cluster_level_shifter_out
  (
   input  logic in_i,
   output logic out_o
   );
   
`ifdef CMOS28FDSOI_8T

    assign out_o = in_i;
   
`endif


`ifdef CMOS28FDSOI_12T_UWVR
   C12T32DG_LLU_LSINX26 
     lsout
       (
	.Z(out_o), 
	.A(in_i)
	);
`endif 
   
endmodule

// UWVR VOLTAGES ARE INVERTED: VDDI = VOUT, VDDO = VIN
// C12T32DG_LLU_LSINX26

module pulp_level_shifter_out
  (
   input  logic in_i,
   output logic out_o
   );
   
   C12T32DG_LLU_LSINX26 
     lsout
       (
	.Z(out_o), 
	.A(in_i)
	);
   
endmodule

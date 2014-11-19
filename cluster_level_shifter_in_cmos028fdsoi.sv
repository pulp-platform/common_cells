
// C12T32_LLN2U4S_BFX16

module cluster_level_shifter_in
  (
   input  logic in_i,
   output logic out_o
   );
   
   C12T32_LLN2U4S_BFX16
     lsin
       (
	.Z(out_o),
	.A(in_i)
	);
   
endmodule

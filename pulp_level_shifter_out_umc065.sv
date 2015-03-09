
module pulp_level_shifter_out
  (
   input  logic in_i,
   output logic out_o
   );


   BUFM20W
     lsout
       (
	.Z(out_o),
	.A(in_i)
	);


   
endmodule

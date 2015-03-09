
module cluster_level_shifter_in
  (
   input  logic in_i,
   output logic out_o
   );
   

   BUFM20W
     lsin
       (
	.Z(out_o),
	.A(in_i)
	);
   
endmodule

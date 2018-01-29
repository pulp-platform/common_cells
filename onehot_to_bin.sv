// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Franceco Conti <fconti@iis.ee.ethz.ch>

module onehot_to_bin (onehot,bin);
   
   parameter ONEHOT_WIDTH = 16;
   parameter BIN_WIDTH    = $clog2(ONEHOT_WIDTH);
   
   input [ONEHOT_WIDTH-1:0] onehot;
   output [BIN_WIDTH-1:0]   bin;
   
   genvar 		    i,j;
   generate
      for (j=0; j<BIN_WIDTH; j=j+1)
	begin : jl
	   wire [ONEHOT_WIDTH-1:0] tmp_mask;
	   for (i=0; i<ONEHOT_WIDTH; i=i+1)
	     begin : il
		wire [BIN_WIDTH-1:0] tmp_i;
		assign tmp_i = i;
		assign tmp_mask[i] = tmp_i[j];
	     end	
	   assign bin[j] = |(tmp_mask & onehot);
	end
   endgenerate
   
endmodule

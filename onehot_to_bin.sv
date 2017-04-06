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

module onehot_to_bin (onehot,bin);


parameter ONEHOT_WIDTH = 16;
parameter BIN_WIDTH    = $clog2(ONEHOT_WIDTH);

input [ONEHOT_WIDTH-1:0] onehot;
output [BIN_WIDTH-1:0] bin;

genvar i,j;
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
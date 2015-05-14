module pulp_clock_gating_async
(
    input  logic clk_i,
    input  logic rstn_i,
    input  logic en_async_i,
    input  logic test_en_i,
    output logic clk_o
);

    logic     clk_en;
    logic     r_sync_0;
    logic     r_sync_1;
    
    always_ff @ (posedge clk_i or negedge rstn_i)
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

    always_latch
    begin
      if (clk_i == 1'b0)
        clk_en <= r_sync_1 | test_en_i;
    end

    assign clk_o = clk_i & clk_en;

endmodule

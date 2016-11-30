module pulp_clock_gating_async
(
    input  logic clk_i,
    input  logic rstn_i,
    input  logic en_async_i,
    output logic en_ack_o,
    input  logic test_en_i,
    output logic clk_o
);

    logic     r_sync_0;
    logic     r_sync_1;

    assign en_ack_o = r_sync_1;
    
    always_ff @ (posedge clk_i or negedge rstn_i)
    begin
        if(~rstn_i)
        begin
            r_sync_0 <= 1'b0;
            r_sync_1 <= 1'b0;
        end
        else
        begin
            r_sync_0 <= en_async_i;
            r_sync_1 <= r_sync_0;
        end
    end

    pulp_clock_gating i_clk_gate
    (
        .clk_i    ( clk_i     ),
        .en_i     ( r_sync_1  ),
        .test_en_i( test_en_i ),
        .clk_o    ( clk_o     )
    );

endmodule

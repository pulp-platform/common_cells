
module cluster_level_shifter_out_clamp
(
    input  logic in_i,
    output logic out_o,
    input  logic clamp_i
);

    assign out_o = clamp_i ? 1'b0 : in_i;

endmodule

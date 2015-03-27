
module cluster_level_shifter_out_clamp
(
    input  logic in_i,
    output logic out_o,
    input logic  clamp_i
);


    SHIFT_IN_EN_X10  lsout
    (
        .Z(out_o),
        .A(in_i),
        .R(clamp_i)
    );
endmodule

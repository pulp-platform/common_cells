module pulp_buffer
(
    input  logic in_i,
    output logic out_o
);

    C8T28SOI_LR_BFX19_P0 buf_i
    (
        .A(in_i),
        .Z(out_o)
    );

endmodule

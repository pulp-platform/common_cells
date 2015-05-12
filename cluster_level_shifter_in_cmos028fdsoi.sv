
// C12T32_LLN2U4S_BFX16

`include "ulpsoc_defines.sv"

module cluster_level_shifter_in
(
    input  logic in_i,
    output logic out_o
);

`ifdef CMOS28FDSOI_8T
    C8T28SOIDV_LRV_LSINX32 lsin
    (
        .Z(out_o),
        .A(in_i),
    );
`endif


`ifdef CMOS28FDSOI_12T_UWVR
    C12T32_LLN2U4S_BFX16 lsin
    (
        .Z(out_o),
        .A(in_i)
    );
`endif 

endmodule

// LL
// C12T28SOI_LL_CNBFX38_P0
// C12T28SOI_LL_CNBFX38_P4
// C12T28SOI_LL_CNBFX38_P10
// C12T28SOI_LL_CNBFX38_P16
// LR
// C12T28SOI_LR_CNBFX38_P0
// C12T28SOI_LR_CNBFX38_P4
// C12T28SOI_LR_CNBFX38_P10
// UWVR
// C12T32_LLUP10_CNBFX36
//
// 8T RVT
// C8T28SOI_LR_CNBFX37_P0
// C8T28SOI_LR_CNBFX37_P4
// C8T28SOI_LR_CNBFX37_P10
// C8T28SOI_LR_CNBFX37_P16

`include "ulpsoc_defines.sv"

module pulp_clock_buffer
(
    input  logic clk_i,
    output logic clk_o
);

`ifdef CMOS28FDSOI_8T
    C8T28SOI_LR_CNBFX37_P0  clk_buf_i
    (
        .A(clk_i),
        .Z(clk_o)
    );
`endif


`ifdef CMOS28FDSOI_12T_UWVR
    C12T32_LLUP10_CNBFX36 clk_buf_i
    (
        .A(clk_i),
        .Z(clk_o)
    );
`endif
endmodule

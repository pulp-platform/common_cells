module pulp_apb_protocol_adapter #(
  parameter APB_ADDR_WIDTH = 32,
  parameter APB_DATA_WIDTH = 32 )
(
  input  logic    pclk_i,
  input  logic    prst_ni,

  APB_BUS.Slave   apb_pulp,
  APB_BUS.Master  apb_amba
);
  
  assign apb_amba.pwrite  = apb_pulp.pwrite;
  assign apb_amba.paddr   = apb_pulp.paddr;
  assign apb_amba.pwdata  = apb_pulp.pwdata;

  assign apb_pulp.pslverr = apb_amba.pslverr;
  assign apb_pulp.prdata  = apb_amba.prdata;

  enum logic [1:0] { IDLE, ACCESS, ACCESS_DONE } apb_state_cs, apb_state_ns;

  always_comb begin
    apb_state_ns      = apb_state_cs;
    apb_amba.psel     = 1'b0;
    apb_amba.penable  = 1'b0;
    apb_pulp.pready   = 1'b0;

    case (apb_state_cs)
      IDLE: begin
        if (apb_pulp.psel & apb_pulp.penable) begin
          apb_amba.psel = 1'b1;
          apb_state_ns  = ACCESS;
        end
      end
      ACCESS:begin
        apb_amba.psel     = 1'b1;
        apb_amba.penable  = 1'b1;
        apb_pulp.pready   = apb_amba.pready;
        if (apb_amba.pready)
          apb_state_ns    = ACCESS_DONE;
      end
      ACCESS_DONE: begin
        if (apb_pulp.psel & apb_pulp.penable) begin
          apb_amba.psel = 1'b1;
          apb_state_ns  = ACCESS;
        end
        else
          apb_state_ns = IDLE;
      end
    endcase
  end

  always_ff @(posedge pclk_i, negedge prst_ni) begin
    if(~prst_ni) begin
      apb_state_cs <= IDLE;
    end
    else begin
      apb_state_cs <= apb_state_ns;
    end
  end

endmodule
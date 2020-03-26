module usb_reset_synchronizer (
  input  logic clk_i,
  input  logic rst_ni,

  input  logic test_mode_en_i,
  input  logic test_rst_ni,

  output logic rst_no
);

  rstgen rstgen_i (
    .clk_i        ( clk_i          ),
    .rst_ni       ( rst_ni         ),
    .test_mode_i  ( test_mode_en_i ),
    .init_no      (                ),
    .rst_no       ( rst_no         )
  );

endmodule

module min_max_tree #(
  parameter int unsigned NumIn     = 32'd32,
  parameter int unsigned DataWidth = 32'd32,
  parameter type         data_t    = logic[DataWidth-1:0],
  parameter int unsigned IdxWidth  = (NumIn > 32'd1) ? unsigned'($clog2(NumIn)) : 32'd1,
  parameter type         idx_t     = logic [IdxWidth-1:0]
)(
  input  data_t [NumIn-1:0] data_i,
  input  logic  [NumIn-1:0] valid_i,
  input  logic              is_max_i,

  output data_t             data_o,
  output logic              valid_o,
  output idx_t              idx_o
);

  /// Number of Inputs rounded to power of 2
  localparam int unsigned NumTreeInputs = 1 << IdxWidth;

  /// payload
  typedef struct packed {
    idx_t  idx;
    data_t data;
    logic  valid;
  } payload_t;

  // internal payload
  payload_t [2*NumTreeInputs-2:0] payload_int;

  // generate the internal layers
  always_comb begin : proc_compare

    // variables to point to base indexes of the temporary array
    automatic int unsigned inp_base_idx = 32'd0;
    automatic int unsigned oup_base_idx = NumTreeInputs;

    // default
    payload_int = '0;

    // assign input connections
    for (int unsigned inp = 0; inp < NumIn; inp++) begin
      payload_int[inp].idx   = idx_t'(inp);
      payload_int[inp].data  = data_i[inp];
      payload_int[inp].valid = valid_i[inp];
    end

    // add the comps
    for (int unsigned level = IdxWidth; level != 0; level--) begin
      // connect the intermediate layer
      for (int unsigned i = 0; i < (1 << (level-1)); i++) begin
        // helper signals
        automatic payload_t inp_left  = payload_int[inp_base_idx+2*i];
        automatic payload_t inp_right = payload_int[inp_base_idx+2*i+1];
        //
        // if one is valid and the other not; choose this one
        if (inp_left.valid & !inp_right.valid) begin
          if (is_max_i) begin
            payload_int[oup_base_idx+i] = inp_left;
          end else begin
            payload_int[oup_base_idx+i] = inp_right;
          end
        // and the other ones
        end else if (!inp_left.valid & inp_right.valid) begin
          if (is_max_i) begin
            payload_int[oup_base_idx+i] = inp_right;
          end else begin
            payload_int[oup_base_idx+i] = inp_left;
          end
        // we have to compare
        end else begin
          // left is bigger or equal -> equality use the one with lower ID
          if (inp_left.data > inp_right.data) begin
            payload_int[oup_base_idx+i] = inp_left;
            // right is bigger
          end else if (inp_left.data < inp_right.data) begin
            payload_int[oup_base_idx+i] = inp_right;
          end else begin
            payload_int[oup_base_idx+i] = inp_left;
          end
        end
      end
      // update base indeces
      inp_base_idx = inp_base_idx + (1 << (level));
      oup_base_idx = oup_base_idx + (1 << (level-1));
    end
  end

  // assign the output
  assign data_o  = payload_int[2*NumTreeInputs-2].data;
  assign valid_o = payload_int[2*NumTreeInputs-2].valid;
  assign idx_o   = payload_int[2*NumTreeInputs-2].idx;

endmodule

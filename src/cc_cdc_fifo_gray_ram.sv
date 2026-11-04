// Copyright 2026 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Kuan-Yu Liu <ana.liu@mail.utoronto.ca>

/// A clock domain crossing FIFO using gray counters, with the FIFO storage in
/// a single dual-clock memory. Drop-in alternative to `cc_cdc_fifo_gray` for
/// FPGA targets (same ports, same parameters, same reset requirements).
///
/// # Why
///
/// `cc_cdc_fifo_gray` keeps the FIFO contents in a register array inside the
/// source half and exposes the *entire* array to the destination half over
/// the `async_data` bundle, where a read mux selects one entry. That is fine
/// for ASIC, but on FPGAs nothing can be inferred as block RAM: every entry
/// is a flip-flop, the write enable fans out to the whole array and the read
/// side is a depth-wide mux (see pulp-platform/axi issue #294).
///
/// # Architecture
///
/// The gray-pointer CDC is unchanged and reused verbatim: the write pointer
/// is managed in the source domain (`cc_cdc_fifo_gray_src_ptr`), the read
/// pointer in the destination domain (`cc_cdc_fifo_gray_dst_ptr`), and the
/// pointers are gray coded and passed through multi-stage synchronizers.
///
/// What changes is the storage: a memory written on `src_clk_i` and read
/// synchronously on `dst_clk_i`, coded so that FPGA tools infer a simple
/// dual-port, dual-clock RAM (M20K/MLAB on Intel, BRAM/LUTRAM on AMD). The
/// read has a read enable, so the memory's output register doubles as the
/// FIFO's one-entry output buffer: it holds data and `dst_valid_o` while the
/// consumer is not ready.
///
/// Read pointer timing: the read pointer advances when a memory read is
/// *issued* (`rd_en`), i.e. when the FIFO is not empty and the output
/// buffer is free or being drained this cycle. Consumption by the consumer
/// (`dst_valid_o & dst_ready_i`) is a separate handshake on the output
/// buffer. `dst_valid_o` is registered and never depends combinationally on
/// `dst_ready_i`.
///
/// # Differences to `cc_cdc_fifo_gray`
///
/// * Total buffering is 2**LogDepth + 1 entries (memory + output register);
///   `cc_cdc_fifo_gray` buffers 2**LogDepth + 2 (array + 2-entry spill
///   register). Data order and content are identical; the cycle on which
///   `src_ready_o` de-asserts under back-pressure can differ by one entry.
/// * Memory contents are not reset (only pointers, synchronizers and the
///   output valid are). The output data register is likewise not reset and
///   is qualified by `dst_valid_o`.
/// * The data no longer crosses the clock boundary on asynchronous nets, so
///   the `set_max_delay`/`set_false_path` constraints of `cc_cdc_fifo_gray`
///   apply to the pointer nets only -- as long as the tool maps `mem` to a
///   RAM block. For very small arrays a tool may keep `mem` in registers
///   (Quartus did so for a 4 x 7-bit instance); the `mem` -> read mux ->
///   `rdata_q` path is then a data crossing like the original's and needs
///   the same bound (e.g. `set_data_delay` / `set_max_delay`). Check the
///   RAM report of the implementation.
///
/// # Reset
///
/// Same rules as `cc_cdc_fifo_gray`: this module is for power-on reset.
/// Assert `src_rst_ni` and `dst_rst_ni` simultaneously (asynchronously) and
/// de-assert each synchronously to its own clock. Warm reset of one side
/// only is NOT supported.
///
/// # Constraints
///
/// ```
/// set_ungroup [get_designs cc_cdc_fifo_gray_ram*] false
/// set_boundary_optimization [get_designs cc_cdc_fifo_gray_ram*] false
/// set_max_delay min(T_src, T_dst) \
///     -through [get_pins -hierarchical -filter async] \
///     -through [get_pins -hierarchical -filter async]
/// set_false_path -hold \
///     -through [get_pins -hierarchical -filter async] \
///     -through [get_pins -hierarchical -filter async]
/// ```

`include "common_cells/assertions.svh"

(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_ram #(
  /// The width of the default logic type.
  parameter int unsigned Width = 1,
  /// The data type of the payload transported by the FIFO.
  parameter type data_t = logic [Width-1:0],
  /// The FIFO's depth given as 2**LogDepth (memory entries, excluding the
  /// one-entry output register).
  parameter int unsigned LogDepth = 3,
  /// The number of synchronization registers to insert on the async pointers.
  parameter int unsigned SyncStages = 2
) (
  input  logic  src_rst_ni,
  input  logic  src_clk_i,
  input  data_t src_data_i,
  input  logic  src_valid_i,
  output logic  src_ready_o,

  input  logic  dst_rst_ni,
  input  logic  dst_clk_i,
  output data_t dst_data_o,
  output logic  dst_valid_o,
  input  logic  dst_ready_i
);

  localparam int unsigned Depth     = 2**LogDepth;
  localparam int unsigned DataWidth = $bits(data_t);

  // Pointer nets crossing the clock boundary (same names as in
  // cc_cdc_fifo_gray, so the same testbench monitors apply).
  logic [LogDepth:0]   async_wptr, async_rptr;
  logic [LogDepth-1:0] src_widx, dst_ridx;
  logic                src_write;
  logic                fifo_not_empty, out_free, rd_en;

  // ---------------------------------------------------------------------------
  // Source domain: write pointer + full flag (unchanged from cc_cdc_fifo_gray)
  // ---------------------------------------------------------------------------
  cc_cdc_fifo_gray_src_ptr #(
    .LogDepth   ( LogDepth   ),
    .SyncStages ( SyncStages )
  ) i_src_ptr (
    .src_rst_ni,
    .src_clk_i,
    .src_valid_i,
    .src_ready_o,
    .src_widx_o   ( src_widx   ),
    (* async *) .async_wptr_o ( async_wptr ),
    (* async *) .async_rptr_i ( async_rptr )
  );

  assign src_write = src_valid_i & src_ready_o;

  // ---------------------------------------------------------------------------
  // Destination domain: read pointer + empty flag (unchanged from
  // cc_cdc_fifo_gray). The pointer advances on `rd_en`, i.e. when a memory
  // read is issued, not when the consumer takes the data.
  // ---------------------------------------------------------------------------
  cc_cdc_fifo_gray_dst_ptr #(
    .LogDepth   ( LogDepth   ),
    .SyncStages ( SyncStages )
  ) i_dst_ptr (
    .dst_rst_ni,
    .dst_clk_i,
    .dst_ready_i  ( out_free       ),
    .dst_valid_o  ( fifo_not_empty ),
    .dst_ridx_o   ( dst_ridx       ),
    (* async *) .async_wptr_i ( async_wptr ),
    (* async *) .async_rptr_o ( async_rptr )
  );

  // The output register is free when it is empty or being drained this cycle.
  assign out_free = ~dst_valid_o | dst_ready_i;
  assign rd_en    = fifo_not_empty & out_free;

  // ---------------------------------------------------------------------------
  // Storage: simple dual-port, dual-clock memory.
  // Write port clocked by src_clk_i, read port clocked by dst_clk_i with a
  // read enable; no reset on the array or on the read data register. This is
  // the coding style FPGA tools infer as dual-clock block RAM (verified with
  // Quartus Prime Pro 23.2 on Arria 10: M20K, read enable connected; the AMD
  // simple dual-port template is the same but was not tested).
  // The gray-pointer protocol guarantees a location is never read while it is
  // being written, so read-during-write behaviour of the memory is irrelevant.
  // ---------------------------------------------------------------------------
  logic [DataWidth-1:0] mem [Depth];
  logic [DataWidth-1:0] rdata_q;
  logic                 valid_q;

  always_ff @(posedge src_clk_i) begin
    if (src_write) begin
      mem[src_widx] <= DataWidth'(src_data_i);
    end
  end

  always_ff @(posedge dst_clk_i) begin
    if (rd_en) begin
      rdata_q <= mem[dst_ridx];
    end
  end

  // Output valid: set when a read is issued, cleared when the consumer takes
  // the entry and no new read refills the register in the same cycle.
  always_ff @(posedge dst_clk_i or negedge dst_rst_ni) begin
    if (!dst_rst_ni) begin
      valid_q <= 1'b0;
    end else if (rd_en) begin
      valid_q <= 1'b1;
    end else if (dst_ready_i) begin
      valid_q <= 1'b0;
    end
  end

  assign dst_valid_o = valid_q;
  assign dst_data_o  = data_t'(rdata_q);

  // Check the invariants.
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(log_depth_0, LogDepth > 0)
  `ASSERT_INIT(sync_stages_gt_2, SyncStages >= 2)
  `endif

endmodule

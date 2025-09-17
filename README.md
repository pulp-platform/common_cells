[![Build Status](https://github.com/pulp-platform/common_cells/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/pulp-platform/common_cells/actions/workflows/ci.yml?query=branch%3Amaster)
[![GitHub tag (latest SemVer)](https://img.shields.io/github/v/tag/pulp-platform/common_cells?color=blue&label=current&sort=semver)](CHANGELOG.md)
[![SHL-0.51 license](https://img.shields.io/badge/license-SHL--0.51-green)](LICENSE)

# Common Cells Repository

Maintainer: Nils Wistoff <nwistoff@iis.ee.ethz.ch>

This repository contains commonly used cells and headers for use in various projects.

## Cell Contents

This repository currently contains the following cells, ordered by categories.
Please note that cells with status *deprecated* are not to be used for new designs and only serve to provide compatibility with old code.

### Clocks and Resets

| Name                                                               | Description                                                                           | Status       | Superseded By                       |
|--------------------------------------------------------------------|---------------------------------------------------------------------------------------|--------------|-------------------------------------|
| [`clk_int_div`](src/clk_int_div.sv)                                | Arbitrary integer clock divider with config interface and 50% output clock duty cycle | active       |                                     |
| [`clk_int_div_static`](src/clk_int_div_static.sv)                  | A convenience wrapper around `clk_int_div` with static division factor.               | active       |                                     |
| [`clk_div`](src/deprecated/clk_div.sv)                             | Clock divider with integer divisor                                                    | *deprecated* | [`clk_int_div`](src/clk_int_div.sv) |
| [`clock_divider`](src/deprecated/clock_divider.sv)                 | Clock divider with configuration registers                                            | *deprecated* | [`clk_int_div`](src/clk_int_div.sv) |
| [`clock_divider_counter`](src/deprecated/clock_divider_counter.sv) | Clock divider using a counter                                                         | *deprecated* | [`clk_int_div`](src/clk_int_div.sv) |
| [`rstgen`](src/rstgen.sv)                                          | Reset synchronizer                                                                    | active       |                                     |
| [`rstgen_bypass`](src/rstgen_bypass.sv)                            | Reset synchronizer with dedicated test reset bypass                                   | active       |                                     |

### Clock Domains and Asynchronous Crossings

| Name                                                                  | Description                                                                                   | Status       | Superseded By                     |
|-----------------------------------------------------------------------|-----------------------------------------------------------------------------------------------|--------------|-----------------------------------|
| [`cdc_4phase`](src/cdc_4phase.sv)                                     | Clock domain crossing using 4-phase handshake, with ready/valid interface                     | active       |                                   |
| [`cdc_2phase`](src/cdc_2phase.sv)                                     | Clock domain crossing using two-phase handshake, with ready/valid interface                   | active       |                                   |
| [`cdc_2phase_clearable`](src/cdc_2phase_clearable.sv)                 | Identical to `cdc_2phase` but supports one-sided async/sync resetting of either src or dst    | active       |                                   |
| [`cdc_fifo_2phase`](src/cdc_fifo_2phase.sv)                           | Clock domain crossing FIFO using two-phase handshake, with ready/valid interface              | active       |                                   |
| [`cdc_fifo_gray`](src/cdc_fifo_gray.sv)                               | Clock domain crossing FIFO using a gray-counter, with ready/valid interface                   | active       |                                   |
| [`cdc_fifo_gray_clearable`](src/cdc_fifo_gray_clearable.sv)           | Identical to `cdc_fifo_gray` but supports one-sided async/sync resetting of either src or dst | active       |                                   |
| [`cdc_reset_ctrlr`](src/cdc_reset_ctrlr.sv)                           | Lock-step reset sequencer accross clock domains (internally used by clearable CDCs)           | active       |                                   |
| [`clk_mux_glitch_free`](src/clk_mux_glitch_free.sv)                   | A glitch-free clock multiplexer with parametrizeable number of inputs.                        | active       |                                   |
| [`edge_detect`](src/edge_detect.sv)                                   | Rising/falling edge detector                                                                  | active       |                                   |
| [`edge_propagator`](src/edge_propagator.sv)                           | Propagates a single-cycle pulse across an asynchronous clock domain crossing                  | active       |                                   |
| [`edge_propagator_ack`](src/edge_propagator_ack.sv)                   | `edge_propagator` with sender-synchronous acknowledge pin (flags received pulse)              | active       |                                   |
| [`edge_propagator_rx`](src/edge_propagator_rx.sv)                     | Receive slice of `edge_propagator`, requires only the receiver clock                          | active       |                                   |
| [`edge_propagator_tx`](src/edge_propagator_tx.sv)                     | Transmit slice of `edge_propagator`, requires only the sender clock                           | active       |                                   |
| [`isochronous_spill_register`](src/isochronous_spill_register.sv)     | Isochronous clock domain crossing and full handshake (like `spill_register`)                  | active       |                                   |
| [`isochronous_4phase_handshake`](src/isochronous_4phase_handshake.sv) | Isochronous four-phase handshake.                                                             | active       |                                   |
| [`pulp_sync`](src/deprecated/pulp_sync.sv)                            | Serial line synchronizer                                                                      | *deprecated* | [`sync`](src/sync.sv)             |
| [`pulp_sync_wedge`](src/deprecated/pulp_sync_wedge.sv)                | Serial line synchronizer with edge detector                                                   | *deprecated* | [`sync_wedge`](src/sync_wedge.sv) |
| [`serial_deglitch`](src/serial_deglitch.sv)                           | Serial line deglitcher                                                                        | active       |                                   |
| [`sync`](src/sync.sv)                                                 | Serial line synchronizer                                                                      | active       |                                   |
| [`sync_wedge`](src/sync_wedge.sv)                                     | Serial line synchronizer with edge detector                                                   | active       |                                   |

### Counters and Shift Registers

| Name                                                       | Description                                                         | Status       | Superseded By                   |
| ---------------------------------------------------------- | ------------------------------------------------------------------- | ------------ | ------------------------------- |
| [`counter`](src/counter.sv)                                | Generic up/down counter with overflow detection                     | active       |                                 |
| [`credit_counter`](src/credit_counter.sv)                  | Up/down counter for credit                                          | active       |                                 |
| [`delta_counter`](src/delta_counter.sv)                    | Up/down counter with variable delta and overflow detection          | active       |                                 |
| [`generic_LFSR_8bit`](src/deprecated/generic_LFSR_8bit.sv) | 8-bit linear feedback shift register (LFSR)                         | *deprecated* | [`lfsr_8bit`](src/lfsr_8bit.sv) |
| [`lfsr_8bit`](src/lfsr_8bit.sv)                            | 8-bit linear feedback shift register (LFSR)                         | active       |                                 |
| [`lfsr_16bit`](src/lfsr_16bit.sv)                          | 16-bit linear feedback shift register (LFSR)                        | active       |                                 |
| [`lfsr`](src/lfsr.sv)                                      | 4...64-bit parametric Galois LFSR with optional whitening feature   | active       |                                 |
| [`max_counter`](src/max_counter.sv)                        | Up/down counter with variable delta that tracks its maximum value   | active       |                                 |
| [`mv_filter`](src/mv_filter.sv)                            | **ZARUBAF ADD DESCRIPTION**                                         | active       |                                 |
| [`trip_counter`](src/trip_counter.sv)                      | Counter that resets automatically when it reaches a specified bound | active       |                                 |

### Data Path Elements

| Name                                                           | Description                                                                                               | Status       | Superseded By                       |
|----------------------------------------------------------------|-----------------------------------------------------------------------------------------------------------|--------------|-------------------------------------|
| [`addr_decode`](src/addr_decode.sv)                            | Address map decoder                                                                                       | active       |                                     |
| [`addr_decode_dync`](src/addr_decode_dync.sv)                  | Address map decoder extended to support dynamic online configuration                                      | active       |                                     |
| [`addr_decode_napot`](src/addr_decode_napot.sv)                | Address map decoder using naturally-aligned power of two (NAPOT) regions                                  | active       |                                     |
| [`multiaddr_decode`](src/multiaddr_decode.sv)                  | Address map decoder using NAPOT regions and allowing for multiple address inputs                          | active       |                                     |
| [`ecc_decode`](src/ecc_decode.sv)                              | SECDED Decoder (Single Error Correction, Double Error Detection)                                          | active       |                                     |
| [`ecc_encode`](src/ecc_encode.sv)                              | SECDED Encoder (Single Error Correction, Double Error Detection)                                          | active       |                                     |
| [`binary_to_gray`](src/binary_to_gray.sv)                      | Binary to gray code converter                                                                             | active       |                                     |
| [`find_first_one`](src/deprecated/find_first_one.sv)           | Leading-one finder / leading-zero counter                                                                 | *deprecated* | [`lzc`](src/lzc.sv)                 |
| [`gray_to_binary`](src/gray_to_binary.sv)                      | Gray code to binary converter                                                                             | active       |                                     |
| [`lzc`](src/lzc.sv)                                            | Leading/trailing-zero counter                                                                             | active       |                                     |
| [`onehot_to_bin`](src/onehot_to_bin.sv)                        | One-hot to binary converter                                                                               | active       |                                     |
| [`shift_reg`](src/shift_reg.sv)                                | Shift register for arbitrary types                                                                        | active       |                                     |
| [`shift_reg_gated`](src/shift_reg_gated.sv)                    | Shift register with ICG for arbitrary types                                                               | active       |                                     |
| [`rr_arb_tree`](src/rr_arb_tree.sv)                            | Round-robin arbiter for req/gnt and vld/rdy interfaces with optional priority                             | active       |                                     |
| [`rrarbiter`](src/deprecated/rrarbiter.sv)                     | Round-robin arbiter for req/ack interface with look-ahead                                                 | *deprecated* | [`rr_arb_tree`](src/rr_arb_tree.sv) |
| [`prioarbiter`](src/deprecated/prioarbiter.sv)                 | Priority arbiter arbiter for req/ack interface with look-ahead                                            | *deprecated* | [`rr_arb_tree`](src/rr_arb_tree.sv) |
| [`fall_through_register`](src/fall_through_register.sv)        | Fall-through register with ready/valid interface                                                          | active       |                                     |
| [`spill_register_flushable`](src/spill_register_flushable.sv)  | Register with ready/valid interface to cut all combinational interface paths and additional flush signal. | active       |                                     |
| [`spill_register`](src/spill_register.sv)                      | Register with ready/valid interface to cut all combinational interface paths                              | active       |                                     |
| [`stream_arbiter`](src/stream_arbiter.sv)                      | Round-robin arbiter for ready/valid stream interface                                                      | active       |                                     |
| [`stream_arbiter_flushable`](src/stream_arbiter_flushable.sv)  | Round-robin arbiter for ready/valid stream interface and flush functionality                              | active       |                                     |
| [`stream_demux`](src/stream_demux.sv)                          | Ready/valid interface demultiplexer                                                                       | active       |                                     |
| [`lossy_valid_to_stream`](src/lossy_valid_to_stream.sv)        | Convert Valid-only to ready/valid by updating in-flight transaction                                       | active       |                                     |
| [`stream_join`](src/stream_join.sv)                            | Ready/valid handshake join multiple to one common                                                         | active       |                                     |
| [`stream_join_dynamic`](src/stream_join_dynamic.sv)            | Ready/valid handshake join multiple to one common, dynamically configurable subset selection              | active       |                                     |
| [`stream_mux`](src/stream_mux.sv)                              | Ready/valid interface multiplexer                                                                         | active       |                                     |
| [`stream_register`](src/stream_register.sv)                    | Register with ready/valid interface                                                                       | active       |                                     |
| [`stream_fork`](src/stream_fork.sv)                            | Ready/valid fork                                                                                          | active       |                                     |
| [`stream_fork_dynamic`](src/stream_fork_dynamic.sv)            | Ready/valid fork, with selection mask for partial forking                                                 | active       |                                     |
| [`stream_filter`](src/stream_filter.sv)                        | Ready/valid filter                                                                                        | active       |                                     |
| [`stream_delay`](src/stream_delay.sv)                          | Randomize or delay ready/valid interface                                                                  | active       |                                     |
| [`stream_to_mem`](src/stream_to_mem.sv)                        | Use memories without flow control for output data in streams.                                             | active       |                                     |
| [`stream_xbar`](src/stream_xbar.sv)                            | Fully connected crossbar with ready/valid interface.                                                      | active       |                                     |
| [`stream_omega_net`](src/stream_omega_net.sv)                  | One-way stream omega-net with ready/valid interface. Isomorphic to a butterfly.                           | active       |                                     |
| [`stream_throttle`](src/stream_throttle.sv)                    | Restrict the number of outstanding transfers in a stream.                                                 | active       |                                     |
| [`sub_per_hash`](src/sub_per_hash.sv)                          | Substitution-permutation hash function                                                                    | active       |                                     |
| [`popcount`](src/popcount.sv)                                  | Combinatorial popcount (hamming weight)                                                                   | active       |                                     |
| [`mem_to_banks_detailed`](src/mem_to_banks_detailed.sv)        | Split memory access over multiple parallel banks with detailed response signals                           | active       |                                     |
| [`mem_to_banks`](src/mem_to_banks.sv)                          | Split memory access over multiple parallel banks                                                          | active       |                                     |
| [`heaviside`](src/heaviside.sv)                                | Generates a mask obtained by applying the Heaviside step function                                         | active       |                                     |
| [`boxcar`](src/boxcar.sv)                                      | Generates a mask obtained by applying a boxcar function                                                   | active       |                                     |

### Data Structures

| Name                                                             | Description                                                                 | Status       | Superseded By                                                                                   |
| ---------------------------------------------------------------- | --------------------------------------------------------------------------- | ------------ | ----------------------------------------------------------------------------------------------- |
| [`cb_filter`](src/cb_filter.sv)                                  | Counting-Bloom-Filter with combinational lookup                             | active       |                                                                                                 |
| [`fifo`](src/deprecated/fifo_v1.sv)                              | FIFO register with upper threshold                                          | *deprecated* | [`fifo_v3`](src/fifo_v3.sv)                                                                     |
| [`fifo_v2`](src/deprecated/fifo_v2.sv)                           | FIFO register with upper and lower threshold                                | *deprecated* | [`fifo_v3`](src/fifo_v3.sv)                                                                     |
| [`fifo_v3`](src/fifo_v3.sv)                                      | FIFO register with generic fill counts                                      | active       |                                                                                                 |
| [`passthrough_stream_fifo`](src/passthrough_stream_fifo.sv)      | FIFO register with ready/valid interface and same-cycle push/pop when full  | active       |                                                                                                 |
| [`ring_buffer`](src/ring_buffer.sv)                              | Ring buffer with sequential write and random-access read interfaces         | active       |                                                                                                 |
| [`stream_fifo`](src/stream_fifo.sv)                              | FIFO register with ready/valid interface                                    | active       |                                                                                                 |
| [`stream_fifo_optimal_wrap`](src/stream_fifo_optimal_wrap.sv)    | Wrapper that optimally selects either a spill register or a FIFO            | active       |                                                                                                 |
| [`generic_fifo`](src/deprecated/generic_fifo.sv)                 | FIFO register without thresholds                                            | *deprecated* | [`fifo_v3`](src/fifo_v3.sv)                                                                     |
| [`generic_fifo_adv`](src/deprecated/generic_fifo_adv.sv)         | FIFO register without thresholds                                            | *deprecated* | [`fifo_v3`](src/fifo_v3.sv)                                                                     |
| [`sram`](src/deprecated/sram.sv)                                 | SRAM behavioral model                                                       | *deprecated* | [`tc_sram`](https://github.com/pulp-platform/tech_cells_generic/blob/master/src/rtl/tc_sram.sv) |
| [`plru_tree`](src/plru_tree.sv)                                  | Pseudo least recently used tree                                             | active       |                                                                                                 |
| [`unread`](src/unread.sv)                                        | Empty module to sink unconnected outputs into                               | active       |                                                                                                 |
| [`read`](src/read.sv)                                            | Dummy module that prevents a signal from being removed during synthesis     | active       |                                                                                                 |

## Header Contents

This repository currently contains the following header files.

### RTL Register Macros

The header file [`registers.svh`](include/common_cells/registers.svh) contains macros that expand to descriptions of registers.
To avoid misuse of `always_ff` blocks, only the following macros shall be used to describe sequential behavior.
The use of linter rules that flag explicit uses of `always_ff` in source code is encouraged.

|    Macro     |                             Arguments                             |                                Description                                |
| ------------ | ----------------------------------------------------------------- | ------------------------------------------------------------------------- |
| `` `FF``     | `q_sig`, `d_sig`, `rst_val`, (`clk_sig`, `arstn_sig`)             | Flip-flop with asynchronous active-low reset                              |
| `` `FFAR``   | `q_sig`, `d_sig`, `rst_val`, `clk_sig`, `arst_sig`                | Flip-flop with asynchronous active-high reset                             |
| `` `FFARN``  | `q_sig`, `d_sig`, `rst_val`, `clk_sig`, `arstn_sig`               | *deprecated* Flip-flop with asynchronous active-low reset                 |
| `` `FFSR``   | `q_sig`, `d_sig`, `rst_val`, `clk_sig`, `rst_sig`                 | Flip-flop with synchronous active-high reset                              |
| `` `FFSRN``  | `q_sig`, `d_sig`, `rst_val`, `clk_sig`, `rstn_sig`                | Flip-flop with synchronous active-low reset                               |
| `` `FFNR``   | `q_sig`, `d_sig`, `clk_sig`                                       | Flip-flop without reset                                                   |
|              |                                                                   |                                                                           |
| `` `FFL``    | `q_sig`, `d_sig`, `load_ena`, `rst_val`, (`clk_sig`, `arstn_sig`) | Flip-flop with load-enable and asynchronous active-low reset              |
| `` `FFLAR``  | `q_sig`, `d_sig`, `load_ena`, `rst_val`, `clk_sig`, `arst_sig`    | Flip-flop with load-enable and asynchronous active-high reset             |
| `` `FFLARN`` | `q_sig`, `d_sig`, `load_ena`, `rst_val`, `clk_sig`, `arstn_sig`   | *deprecated* Flip-flop with load-enable and asynchronous active-low reset |
| `` `FFLSR``  | `q_sig`, `d_sig`, `load_ena`, `rst_val`, `clk_sig`, `rst_sig`     | Flip-flop with load-enable and synchronous active-high reset              |
| `` `FFLSRN`` | `q_sig`, `d_sig`, `load_ena`, `rst_val`, `clk_sig`, `rstn_sig`    | Flip-flop with load-enable and synchronous active-low reset               |
| `` `FFLNR``  | `q_sig`, `d_sig`, `load_ena`, `clk_sig`                           | Flip-flop with load-enable without reset                                  |
- *The name of the clock and reset signals for implicit variants is `clk_i` and `rst_ni`, respectively.*
- *Argument suffix `_sig` indicates signal names for present and next state as well as clocks and resets.*
- *Argument `rst_val` specifies the value literal to be assigned upon reset.*
- *Argument `load_ena` specifies the boolean expression that forms the load enable of the register.*

### SystemVerilog Assertion Macros

The header file [`assertions.svh`](include/common_cells/assertions.svh) contains macros that expand to assertion blocks.
These macros should recduce the effort in writing many assertions and make it
easier to use them. They are similar to but incompatible with the macros used by [lowrisc](https://github.com/lowRISC/opentitan/blob/master/hw/ip/prim/rtl/prim_assert.sv).

#### Simple Assertion and Cover Macros
| Macro              | Arguments                                        | Description                                                                |
| ------------------ | ------------------------------------------------ | -------------------------------------------------------------------------- |
| `` `ASSERT_I``     | `__name`, `__prop`, (`__desc`)                   | Immediate assertion                                                        |
| `` `ASSERT_INIT``  | `__name`, `__prop`, (`__desc`)                   | Assertion in initial block. Can be used for things like parameter checking |
| `` `ASSERT_FINAL`` | `__name`, `__prop`, (`__desc`)                   | Assertion in final block                                                   |
| `` `ASSERT``       | `__name`, `__prop`, (`__clk`, `__rst`, `__desc`) | Assert a concurrent property directly                                      |
| `` `ASSERT_NEVER`` | `__name`, `__prop`, (`__clk`, `__rst`, `__desc`) | Assert a concurrent property NEVER happens                                 |
| `` `ASSERT_KNOWN`` | `__name`, `__sig`, (`__clk`, `__rst`, `__desc`)  | Concurrent clocked assertion with custom error message                     |
| `` `COVER``        | `__name`, `__prop`, (`__clk`, `__rst`)           | Cover a concurrent property                                                |
- *The name of the clock and reset signals for implicit variants is `clk_i` and `rst_ni`, respectively.*
- *`__desc` is an optional string argument describing the failure causing the assertion to be violated that is embedded into the error report and defaults to `""`.*

#### Complex Assertion Macros
| Macro                 | Arguments                                                                           | Description                                                                                                |
| --------------------- | ----------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------- |
| `` `ASSERT_PULSE``    | `__name`, `__sig`, (`__clk`, `__rst`, `__desc`)                                     | Assert that signal is an active-high pulse with pulse length of 1 clock cycle                              |
| `` `ASSERT_IF``       | `__name`, `__prop`, `__enable`, (`__clk`, `__rst`, `__desc`)                        | Assert that a property is true only when an enable signal is set                                           |
| `` `ASSERT_KNOWN_IF`` | `__name`, `__sig`, `__enable`, (`__clk`, `__rst`, `__desc`)                         | Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is set          |
| `` `ASSERT_STABLE``   | `__name`, `__valid`, `__ready`, `__data`, `__enable`, (`__clk`, `__rst`, `__desc`)  | Assert that the data on a ready-valid interface is kept stable after valid is asserted, until ready is too |
- *The name of the clock and reset signals for implicit variants is `clk_i` and `rst_ni`, respectively.*
- *`__desc` is an optional string argument describing the failure causing the assertion to be violated that is embedded into the error report and defaults to `""`.*

#### Assumption Macros

| Macro          | Arguments                                        | Description                  |
| -------------- | ------------------------------------------------ | ---------------------------- |
| `` `ASSUME``   | `__name`, `__prop`, (`__clk`, `__rst`, `__desc`) | Assume a concurrent property |
| `` `ASSUME_I`` | `__name`, `__prop`, (`__desc`)                   | Assume an immediate property |
- *The name of the clock and reset signals for implicit variants is `clk_i` and `rst_ni`, respectively.*
- *`__desc` is an optional string argument describing the failure causing the assertion to be violated that is embedded into the error report and defaults to `""`.*

#### Formal Verification Macros

| Macro              | Arguments                                        | Description                                                  |
| ------------------ | ------------------------------------------------ | ------------------------------------------------------------ |
| `` `ASSUME_FPV``   | `__name`, `__prop`, (`__clk`, `__rst`, `__desc`) | Assume a concurrent property during formal verification only |
| `` `ASSUME_I_FPV`` | `__name`, `__prop`, (`__desc`)                   | Assume a concurrent property during formal verification only |
| `` `COVER_FPV``    | `__name`, `__prop`, (`__clk`, `__rst`)           | Cover a concurrent property during formal verification       |
- *The name of the clock and reset signals for implicit variants is `clk_i` and `rst_ni`, respectively.*
- *`__desc` is an optional string argument describing the failure causing the assertion to be violated that is embedded into the error report and defaults to `""`.*

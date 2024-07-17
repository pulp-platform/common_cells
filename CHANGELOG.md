# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## Unreleased
### Added
- `credit_counter`: Add up/down counter for credit.

## 1.36.0 - 2024-07-08
### Fixed
- `registers`: Fix else statement in FFARNC macro.
- `stream_arbiter_flushable`: Do not lock priority arbiter.

## 1.35.0 - 2024-04-22
### Changed
- `id_queue`: Add parameter to cut a critical path.

## 1.34.0 - 2024-04-09
### Changed
- `stream_xbar`: Add payload assertion stability mask.

## 1.33.1 - 2024-03-16
### Fixed
- `stream_omega_net`: Fix assertion.
- Revert gitlab-ci trigger condition to `pull_request`.

## 1.33.0 - 2024-03-07
### Added
- Add `passthrough_stream_fifo`: Stream FIFO which does not cut the timing path, this allows it to do a simultaneous push and pop when full.
- Registers: Add FFARNC macro: Flip-Flop with asynchronous active-low reset and synchronous clear.

### Changed
- Enable assertions in verilator.
- Change `pragma translate_off` statements to ```ifndef SYNTHESIS`` according to IEEE 1364.1-2005 spec 6.3.2.
- `plru_tree`: Add assertion that output is onehot.
- Update CI trigger condition.

### Fixed
- `onehot_to_bin`: Fix width mismatch in assignment.
- `plru_tree`: Improve tool compatibility.
- `stream_xbar`: Fix masked assertion.

## 1.32.0 - 2023-09-26
### Added
- Add `stream_join_dynamic`: `stream_join` with a dynamically configurable subset selection.
- Add `multiaddr_decode`: Address map decoder using NAPOT regions and allowing for multiple address inputs.
- Add `addr_decode_dync`: `addr_decode` with support for dynamic online configuration.

### Changed
- `mem_to_banks`: Change default value for `NumBanks` from `0` to `1` to avoid division by zero.

## 1.31.1 - 2023-08-09
### Fixed
- `mem_to_banks`: Keep defaut values for localparams

## 1.31.0 - 2023-08-08
### Added
- Add `mem_to_banks_detailed`: `mem_to_banks` with detailed response signals

### Fixed
- `unread`: Add dummy signal assignment when targeting Vivado to avoid blackbox inference

## 1.30.0 - 2023-06-09
### Added
- Add `lossy_valid_to_stream`: A converter between valid-only protocols and ready-valid where the latest transaction overwrites the most recently queue one.
- Add `clk_int_div_static`: A wrapper for `clk_int_div` for static clock division.

### Changed
- `popcount`: Refactor and support all input widths.
- `clk_int_div`: Support clock output during reset.
- `stream_delay`: Support larger counts.

### Fixed
- `clk_int_div`: Fix possible deadlock and avoid hold issues.

## 1.29.0 - 2023-04-14
### Added
- Add `shift_reg_gated`: Shift register with ICG for arbitrary types.

### Changed
- CI: Run testbenches in `test/` on internal gitlab mirror.
- `fifo_tb`: Add test for DEPTH not power of two.

### Fixed
- `clk_int_div`: Allow configuration while clock is disabled.
- `mem_to_banks`: Cut possible timing loop for HideStrb feature.
- Improved tool compatibility (Verilator, Questasim, Synopsys).

## 1.28.0 - 2022-12-15
### Added
- Add `clk_mux_glitch_free`: A glitch-free clock multiplexer.

## 1.27.1 - 2022-12-06
### Fixed
- `fall_through_register`: Remove superfluous `$size()` call for tool compatibility

## 1.27.0 - 2022-12-01
### Added
- Add `mem_to_banks`: split memory access over multiple parallel banks. Moved from the `AXI4+ATOP`
  [`axi_to_mem`](https://github.com/pulp-platform/axi/blob/2f395b176bee1c769c80f060a4345fda965bb04b/src/axi_to_mem.sv#L563) module.
- Add `read`: dummy module that prevents a signal from being removed during synthesis

### Changed
- `stream_fifo_optimal_wrap`: Remove asserts
- `fall_through_register`: Update fifo to `fifo_v3`

### Fixed
- FuseSoC: Add `assertions.svh`

## 1.26.0 - 2022-08-26
### Added
- Add `stream_throttle`: restricts the number of outstanding transfers in a stream.

### Changed
- Allow out-of-bounds (i.e. `'0`) top end address in addr_map of `addr_decode` module for end of address space.
- Update CI.

## 1.25.0 - 2022-08-10
### Added
- Add `addr_decode_napot`: variant of `addr_decode` which uses a base address and mask instead of a start and end address.
- Add `stream_fifo_optimal_wrap`: instantiates a more optimal `spill_register` instead of a `stream_fifo` for `depth == 2`.

### Changed
- Make `stream_register` truly stream by replacing internal FIFO with FFs.
- Avoid using `$bits()` call in `id_queue`'s parameters.
- Remove `cb_filter` and `cb_filter_pkg` from from Vivado IP packager project sources due to compatibility issues.
- Use `tc_clk_mux` as glitch-free muxes in `rstgen_bypass` to avoid combinational glitches.
- Avoid program blocks in testbenches for simulator compatibility.

### Fixed
- Update `src_files.yml` and `common_cells.core`

## 1.24.1 - 2022-04-13
### Fixed
- Fix typos in `Bender.yml` and `src_files.yml`

## 1.24.0 - 2022-03-31
### Added
- Add `edge_propagator_ack`: Edge/pulse propagator with sender-synchronous receive-acknowledge
  output.  `edge_propagator` is now implemented by instantiating `edge_propagator_ack`.
- Add `4phase_cdc`: A 4 phase handshaking CDC that allows glitch-free resetting (used internally in the new clearable CDC IPs).
- Add one-sided clearable and/or async resettable flavors of 2phase CDC (`cdc_2phase_clearable`) and gray-counting FIFO CDCs (`cdc_fifo_gray_clearable`).
- Add reset CDC controller `cdc_reset_ctrl` that supports reset/synchronous clear sequencing across clock domain crossings (used internally in clearable CDC IPs).
- Add `clk_int_div` arbitrary integer clock divider with *at-runtime*
  configurable divider selection and glitch-free, 50%duty cycle output clock.
- Add an assertion to the `lzc` to verify parameters.

### Fixed
- Correct reset polarity in assertions in `isochronous_4phase_handshake` and `isochronous_spill_register`
- Fix compatibility of `sub_per_hash` constructs with Verilator

### Changed
- Add `dont_touch` and `async_reg` attribute to FFs in `sync` cell.
- Improved reset behavior documentation (in module header) of existing CDC IPs.
- Deprecated flawed `clk_div` module and add elaboration warning message that
  will be shown for existing designs (can be disabled with optional
  instantiation parameter).
- Add optional `Seed` parameter to `stream_delay` module
- Update `tech_cells_generic` to `0.2.9`

## 1.23.0 - 2021-09-05
### Added
- Add `cc_onehot`
- `isochronous_4phase_handshake`: Isochronous clock domain crossing cutting all paths using a 4-phase handshake.
- Changed `isochronous_spill_register_tb` to `isochronous_crossing_tb` also covering the `isochronous_4phase_handshake`
  module.
- Make reset value of `sync` module parameterizable.

### Changed
- `id_queue`: Allow simultaneous input and output requests in `FULL_BW` mode

## 1.22.1 - 2021-06-14
### Fixed
- Remove breaking change of `spill_register`

## 1.22.0 - 2021-06-09
### Added
- Add `spill_register_flushable`

### Changed
- `registers.svh`: Merge explicit and implicit register variants into `` `FF `` and `` `FFL `` macros
- `rr_arb_tree`: Allow flushing locked decision
- Improved `verific` compatibility

## 1.21.0 - 2021-01-28
### Changed
- Remove `timeprecision/timeunit` arguments
- Update `common_verification` to `0.2.0`
- Update `tech_cells_generic` to `0.2.3`

## 1.20.1 - 2021-01-21
### Changed
- `id_queue`: Replace default or reset value of signals that were assigned `'x` with `'0`.
- `id_queue`: Use `cf_math_pkg::idx_width()` for computation of localparams.

### Fixed
- Add `XSIM` define guard for statements incompatible with `xsim`.

## 1.20.0 - 2020-11-04
### Added
- assertions: Assertion include header with macros (from lowrisc)

### Changed
- `sram.sv`: Deprecated as it has been moved to `tech_cells_generic`

### Fixed
- `stream_register`: Fix `DATA_WIDTH` of instantiated FIFO.
- `stream_xbar`: Add missing argument in assertion error string.
- Lint style fixes
- `stream_omega`: Fix parse issue with verible.
- `src_files.yml`: Fix compile order and missing modules.

## 1.19.0 - 2020-05-25
### Added
- stream_to_mem: Allows to use memories with flow control (req/gnt) for requests but
  without flow control for output data to be used in streams.
- isochronous_spill_register: Isochronous clock domain crossing cutting all paths.
- `rr_arb_tree_tb`: Systemverilog testbench for `rr_arb_tree`, which checks for fair throughput.
- `cf_math_pkg::idx_width`: Constant function for defining the binary representation width
  of an index signal.

### Changed
- `addr_decode`: Use `cf_math_pkg::idx_width` for computing the index width, inline documentation.
- `lzc`: Use `cf_math_pkg::idx_width` for computing the index width, inline documentation.
- `Bender`: Change levels of modules affected by depending on `cf_math_pkg::idx_width()`.
- `stream_xbar`: Fully connected stream bassed interconnect with variable number of inputs and outputs.
- `stream_xbar`: Fully connected stream-bassed interconnect with a variable number of inputs and outputs.
- `stream_omega_net`: Stream-based network implementing an omega topology. Variable number of inputs,
  outputs and radix. Topology is isomorphic to a butterfly network.

### Fixed
- Improve tool compatibility.
- `rr_arb_tree`: Properly degenerate `rr_i` and `idx_o` signals.
- `rr_arb_tree`: Add parameter `FairArb` to distribute throughput of input requests evenly when
  not all inputs have requests active.
- `stream_demux`: Properly degenerate `inp_sel_i` signal.

## 1.18.0 - 2020-04-15
### Added
- stream_fork_dynamic: Wrapper around `stream_fork` for partial forking.
- stream_join: Join multiple Ready/Valid handshakes to one common handshake.
- SECDED (Single Error Correction, Double Error Detection) encoder and decoder
- SECDED Verilator-based testbench
- Travis build for SECDED module

## 1.17.0 - 2020-04-09
### Added
- stream_fifo: Ready/Valid handshake wrapper around `fifo_v3`

## 1.16.4 - 2020-03-02
### Fixed
- id_queue: Fix generation of `head_tail_q` registers

## 1.16.3 - 2020-02-11
### Fixed
- Handle degenerated `addr_decode` with `NoIndices == 1`, change default parameters to `32'd0`

## 1.16.2 - 2020-02-04
### Fixed
- Fix author section in Bender.yml

## 1.16.1 - 2020-02-03
### Fixed
- `rr_arb_tree`: Add guard SVA statement for Verilator
- Added missing sources in `Bender.yml` and `src_files.yml`

## 1.16.0 - 2020-01-13
### Fixed
- Handle degenerated `onehot_to_bin` with `ONEHOT_WIDTH == 1`
- Handle degenerated `id_queue` with `CAPACITY == 1` or `HT_CAPACITY == 1`
- Fix `cdc_fifo_gray` to be a safe clock domain crossing (CDC)

## 1.15.0 - 2019-12-09
### Added
- Added address map decoder module

### Fixed
- Handle degenerated `lzc` with `WIDTH == 1`

## 1.14.0 - 2019-10-08

### Added
- Added spubstitution-permutation hash function module
- Added couning-bloom-filter module
- `spill_register`: Added Bypass parameter
- `counter`: Added sticky overflow
- Added counter with variable delta
- Added counter that tracks its maximum value

### Changed
- Added formal testbench for `fifo` and `fall_through_regsiter`

## 1.13.1 - 2019-06-01

### Changed

- Fix path in `src_files.yml` for `stream_arbiter` and `stream_arbiter_flushable`

## 1.13.0 - 2019-05-29

### Added

- Added exponential backoff window module
- Added parametric Galois LFSR module with optional whitening feature
- Added `cf_math_pkg`: Constant Function implementations of mathematical functions for HDL elaboration

### Changed
- Parametric payload data type for `rr_arb_tree`

### Deprecated
- The following arbiter implementations are deprecated and superseded by `rr_arb_tree`:
- Priority arbiter `prioarbiter`
- Round-robin arbiter `rrarbiter`

### Fixed

## 1.12.0 - 2019-04-09

### Added
- Add priority arbiter
- Add Pseudo Least Recently Used tree
- Add round robin arbiter mux tree

### Changed
- Add selectable arbiter implementation for `stream_arbiter` and `stream_arbiter_flushable`. One can choose between priority (`prio`) and round-robin arbitration (`rr`).
- Add `$onehot0` assertion in one-hot to bin
- Rework `rrarbiter` unit (uses `rr_arb_tree` implementation underneath)

## 1.11.0 - 2019-03-20

### Added
- Add stream fork
- Add fall-through register
- Add stream filter
- Add ID queue

### Changed
- `sync_wedge` use existing synchronizer. This defines a single place where a tech-specific synchronizer can be defined.

### Fixed
- Fix FIFO push and pop signals in `stream_register` to observe interface prerequisites.
- In `fifo_v3`, fix data output when pushing into empty fall-through FIFO. Previously, the data
  output of an empty fall-through FIFO with data at its input (and `push_i=1`) depended on
  `pop_i`: When `pop_i=0`, old, invalid data were visible at the output (even though `empty_o=0`,
  indicating that the data output is valid). Only when `pop_i=1`, the data from the input fell
  through. One consequence of this bug was that `data_o` of the `fall_through_register` could change
  while `valid_o=1`, violating the basic stream specification.

## 1.10.0 - 2018-12-18

### Added
- Add `fifo_v3` with generic fill count
- Add 16 bit LFSR
- Add stream delayer
- Add stream arbiter
- Add register macros for RTL
- Add shift register

### Changed
- Make number of registers of `rstgen_bypass` a parameter.

### Fixed
- Fix `valid_i` and `grant_i` guarantees in `generic_fifo` for backward compatibility.
- LZC: Synthesis of streaming operators in ternary operators
- Add missing entry for `popcount` to `Bender.yml`.
- Add default values for parameters to improve compatibility with Synopsys DC and Vivado.

## 1.9.0 - 2018-11-02

### Added
- Add popcount circuit `popcount`

## 1.8.0 - 2018-10-15

### Added
- Add lock feature to the rrarbiter. This prevents the arbiter to change the decision when we have pending requests that remain unaknowledged for several cycles.
- Add deglitching circuit
- Add generic clock divider
- Add edge detecter as alias to sync_wedge (name is more expressive)
- Add generic counter
- Add moving deglitcher

## 1.7.6 - 2018-09-27

### Added
- Add reset synchronizer with explicit reset bypass in testmode

## 1.7.5 - 2018-09-06
### Fixed
- Fix incompatibility with verilator
- Fix dependency to open-source repo

## 1.7.4 - 2018-09-06
- Fix assertions in `fifo_v2` (write on full / read on empty did not trigger properly)

## 1.7.3 - 2018-08-27
### Fixed
- Use proper `fifo_v2` in `generic_fifo` module.

## 1.7.2 - 2018-08-27
### Added
- Almost full/empty flags to FIFO, as `fifo_v2`.

### Changed
- FIFO moved to `fifo_v1` and instantiates `fifo_v2`.

## 1.7.1 - 2018-08-27
### Fixed
- Revert breaking changes to `fifo`.

## 1.7.0 - 2018-08-24
### Added
- Add stream register (`stream_register`).
- Add stream multiplexer and demultiplexer (`stream_mux`, `stream_demux`).
- Add round robin arbiter (`rrarbiter`).
- Add leading zero counter (`lzc`).

### Changed
- Deprecate `find_first_one` in favor of `lzc`.

## 1.6.0 - 2018-04-03
### Added
- Add binary to Gray code converter.
- Add Gray code to binary converter.
- Add Gray code testbench.
- Add CDC FIFO based on Gray counters. This is a faster alternative to the 2-phase FIFO which also works if a domain's clock has stopped.

### Changed
- Rename `cdc_fifo` to `cdc_fifo_2phase`.
- Adjust CDC FIFO testbench to cover both implementations.

## 1.5.4 - 2018-03-31
### Changed
- Replace explicit clock gate in `fifo` with implicit one.

## 1.5.3 - 2018-03-16
### Changed
- Remove duplicate deprecated modules.

## 1.5.2 - 2018-03-16
### Changed
- Remove deprecated `rstgen` and fix interface.

## 1.5.1 - 2018-03-16
### Changed
- Remove deprecated `onehot_to_bin`.

## 1.5.0 - 2018-03-14
### Added
- Add behavioural SRAM model

## 1.4.0 - 2018-03-14
### Added
- Clock domain crossing FIFO

### Changed
- Re-name new sync modules to resolve namespace collisions

## 1.3.0 - 2018-03-12
### Added
- 2-phase clock domain crossing
- Add old common cells as deprecated legacy modules

## 1.2.3 - 2018-03-09
### Added
- Backwards compatibility wrapper for `generic_LFSR_8bit`

## 1.2.2 - 2018-03-09
### Added
- Backwards compatibility wrapper for `generic_fifo`

## 1.2.1 - 2018-03-09
### Fixed
- Fix an issue in the spill register which causes transactions to be lost

## 1.2.0 - 2018-03-09
### Added
- Add spill register

## 1.1.0 - 2018-03-06
### Added
- Find first zero

## 1.0.0 - 2018-03-02
### Added
- Re-implementation of the generic FIFO supporting all kinds of use-cases
- Testbench for FIFO

### Changed
- Re-formatting and artistic code clean-up

## 0.1.0 - 2018-02-23
### Added
- Fork of PULP common cells repository

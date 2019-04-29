# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## Unreleased

### Added

- Added exponential backoff window module

### Changed
- Parametric payload data type for `rr_arb_tree`

### Deprecated
- The following arbiter implementations are deprecated and superseded by `rr_arb_tree`:
  - Priority arbiter `prioarbiter`
  - Round-robin arbiter `rrarbiter`
  - Stream arbiter `stream_arbiter`
  - Flushable stream arbiter `stream_arbiter_flushable`

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

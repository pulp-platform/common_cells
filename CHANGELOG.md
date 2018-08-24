# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## Unreleased
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

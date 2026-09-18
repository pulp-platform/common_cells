# Formal Verification Properties
These formal properties (`*_properties.sv`) and scripts (`*.sby`) are used for
formal verification of `common_cells` IPs and are meant to be used with
`SymbiYosys`.

## Note on Tools
Make sure you have the commercial `Yosys` and `SymbiYosys`version installed and
in your path or point the `YOSYS` and `SBY` variable to it. We have tested it
with the Symbiotic EDA Edition [20190105A]. Note that the FOSS version won't
work because its SystemVerilog parser does not support all the required
features.

## Usage
Call `make all` to run all tests.

### ECC
The `ecc` target proves the four cases documented in the header of
`cc_ecc_decode.sv` for the `cc_ecc_encode`/`cc_ecc_decode` pair, over a set of
`DataWidth` values chosen to bracket every parity-width transition that proves
quickly. `make all` runs its `cover` task as well as the proof: the properties
constrain where the injected bit errors may land, and the cover task is what
shows those positions are reachable, so a proof resting on an unsatisfiable
assumption cannot pass unnoticed.

To repeat the proof over every parity-width transition up to the module default
of `DataWidth` 64, which took around 45 minutes in one local run and is not
part of `make all`:

    sby -f ecc.sby sweep


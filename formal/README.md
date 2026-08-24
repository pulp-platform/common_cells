# Formal Verification Properties

The files in this directory contain the formal properties and SymbiYosys
configurations for selected `common_cells` modules. The flow is intended for
the open-source OSEDA tool distribution.

## Prerequisites

Install and place these tools in `PATH` (or override their Make variables):

- GNU Make
- `flock` from util-linux
- Yosys and SymbiYosys (`yosys` and `sby`)
- Bender (`bender`), used to select formal sources and generate the shared
  file list
- The solver backends selected by the `.sby` files (SMT solvers and ABC)

The formal configurations require the Yosys Slang plugin to be available to
`sby` as `slang.so`.

## Targets

The eight active proof targets are:

`fifo.check`, `counter.check`, `delta_counter.check`,
`fall_through_register.check`, `lzc.check`,
`cdc_reset_ctrlr_half.check`, `cdc_reset_ctrlr_composed.check`, and
`heaviside.check`.

Run an individual proof from this directory, for example:

```sh
make lzc.check
```

`make all` runs all eight targets. Each run stores its SymbiYosys work files,
solver results, traces, and `<target>.check` success marker below
`formal/build/<target>/`. The FIFO, counter, delta-counter,
fall-through-register, and both CDC reset-controller targets keep their safety
and cover runs in `prove/` and `cover/` subdirectories. The generated, shared
Bender file list is `formal/build/formal.flist`; Bender selects package sources,
active formal properties, and harnesses for the `formal` and
`cc_no_deprecated` targets.

The file list is intentionally regenerated on every requested Make invocation.
Generation is serialized and atomically replaces the shared list, so concurrent
Make invocations cannot expose a partial file. Consequently, a requested target
reruns after source edits instead of reusing a stale PASS marker. No RTL,
include, or property dependency list is maintained in the Makefile.

The FIFO and fall-through register safety tasks use an engine portfolio.
ABC PDR supplies the unbounded reachability proof; SMTBMC checks a bounded
prefix but can be stopped when PDR completes first. Their separate
public-interface reference state is not necessarily k-inductive from
unreachable state pairings, so an SMTBMC induction failure does not by itself
indicate a DUT counterexample when the PDR engine proves the task.

PDR is the safety boundary: it proves that no reachable state violates an
assertion. Cover tasks are bounded exploration checks and do not establish an
unbounded liveness guarantee. The `async2sync` preparation step means reset
behavior is proved at formal clock samples, not at analog or sub-cycle reset
edges. The CDC reset-controller targets additionally assume each reset asserted
at its first sampled clock and deasserted thereafter. Later asynchronous reset
assertion and reset during an in-flight transaction are deferred to a separate
asynchronous-reset formal model.

For the composed CDC cover task, external isolate/clear acknowledgements are
constrained to equal their requests so the complete sequence is explored with
immediate completion. The safety task instead permits arbitrary completion
latency, a level-sticky acknowledgement during each request, and one sampled
trailing-high cycle after withdrawal; a later request starts a new safety epoch.

Use `make clean` to remove the complete `formal/build` tree and its generated
outputs.

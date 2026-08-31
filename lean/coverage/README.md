# StmtResult-to-Lean Coverage Inventory

This directory owns the maintained, source-derived coverage inventory for the
direct `StmtResult`-to-Lean compiler. It records obligations; it does not claim
that a Rust enum mention is a verified compiler capability.

Generation fingerprints the full Rust/compiler, Lean dependency, example, and
configuration surface before and after extraction, and fails if that source
changes mid-snapshot.

Every inventory row has a nonempty positive-tracer obligation and negative
boundary. `tracer_evidence_state=required` is deliberately not described as
an existing test; only `existing` rows have a current source tracer.
`required_tracer_queue.tsv` is the focused 1,376-row execution backlog.

Generate the inventory from the repository root:

```sh
python3 lean/coverage/build_inventory.py generate
```

Check that the committed artifacts match current source:

```sh
python3 lean/coverage/build_inventory.py check
```

Run the focused generator tests:

```sh
python3 lean/coverage/test_build_inventory.py
python3 -m unittest \
  lean.coverage.test_run_primary_tracer_gate \
  lean.coverage.test_run_checked_examples_gate \
  lean.coverage.test_run_integration_gate \
  lean.coverage.test_kernel_check_examples
```

Rebind the broad integration baseline after Rust sources stabilize:

```sh
python3 lean/coverage/run_integration_gate.py
```

The runner leaves the previous evidence untouched if Cargo fails, source or
binary hashes change during the run, test totals do not reconcile, or the
failure-name set differs from the maintained 20-row ledger.

Regenerate and bind the literal Lean adapter surface in one stable snapshot:

```sh
python3 lean/coverage/run_lean_adapter_gate.py
```

This runner leaves the previous adapter evidence untouched if inventory
generation, olean freshness, source fingerprints, generated-artifact hashes,
or the real Lean `#check` gate changes during the command.

Bind the primary Example 54 verifier/compiler/Lean chain atomically:

```sh
python3 lean/coverage/run_primary_tracer_gate.py
```

The report is replaced only if both release binaries, isolated strict success,
the project-mode trust negative, generated and checked Lean, forbidden-output
scan, and every input/source fingerprint remain stable for the whole command.

When Rust is temporarily unbuildable, bind the independent checked-in Lean
surface without compiling new output:

```sh
python3 lean/coverage/run_checked_examples_gate.py --jobs 4
```

This report separates current Lean/checked-pair kernel health from the Rust
compiler and still fingerprints all 69 source/pair inputs and Lean dependencies.

Run the complete fast audit (generated drift, source reconciliation,
statement/result parity, and hash-bound primary tracer evidence):

```sh
python3 lean/coverage/build_inventory.py audit
```

The audit also rejects `sorry`, `admit`, or project `axiom` declarations in
the imported `lean/Litex` dependency surface before accepting historical
kernel evidence.

Build a non-destructive all-example compiler/kernel matrix (all generated
modules go under `tmp/`, never over the checked-in pairs):

```sh
python3 lean/coverage/kernel_check_examples.py \
  --output-dir tmp/2026-08-30/one-week-tolean-day1/all-generated --jobs 4
```

Before compiling one row, the runner removes only that row's prior generated
file inside the validated tmp output directory. A current compiler failure can
therefore never inherit a stale generated hash or false checked-in match.

The matrix refuses to start unless `Litex.olean`, `Core.olean`, and
`Rules.olean` exist and are at least as new as their sources. It also rechecks
that precondition after the run, because a concurrent build can invalidate the
object cache while examples are being checked. Release compiler and all 69
source/pair inputs are independently fingerprinted before and after the run;
coverage totals are current only when every stability flag is true. The
runner exits nonzero for an unstable fingerprint or stale/missing post-run
olean even if every individually completed example happened to pass.
Before checking examples it also runs a stable-fingerprint release build of
`stmt_result_to_lean_compiler`; Rust sources are fingerprinted through both
the build and matrix, so a merely old-but-unchanged binary cannot claim current
source coverage.
Schema 3 also scans every generated and checked module for proof holes, the
retired universal-object ABI, and `Set.univ`. Explicit `axiom` declarations
are handled separately by `example_trust_boundaries.tsv`, so source-declared
trust is visible without being confused with compiler-invented trust.

The generated artifacts are:

- `inventory.json`: machine-readable rows with source identities, source and
  compiler references, reachability evidence, status, ownership, and the next
  gate;
- `summary.md`: deterministic counts by axis, status, and uncatalogued builtin
  mechanism.
- `typed_builtin_queue.tsv`: one review row per typed stable rule ID, including
  producer, compiler consumer, explicit limitation, and next gate.
- `uncatalogued_builtin_queue.tsv`: one review row per stable uncatalogued rule
  ID, including its Rust symbol, direct producer locations, proposed mechanism
  family, current status, and next gate.
- `builtin_to_lean_route_candidates.tsv`: one row per stable builtin ID joining
  its compiler consumers to function-local literal and dynamic Lean adapter
  candidates. Co-occurrence is deliberately marked as a candidate until an
  exact Result tracer and generated Lean module prove the route.
- `uncatalogued_mechanism_families.md`: the seven migration families with
  used/unused counts, one exact representative producer, and the recommended
  Result/Lean migration pattern.
- `tracer_gate_evidence.json`: hash-bound, layered verifier/compiler/drift/Lean
  evidence for the current primary tracer, including the complete imported
  Lean dependency fingerprint, full Rust-source fingerprint, and exact
  verifier/compiler binary hashes. A generated module can be
  kernel-accepted while the checked-in pair still has source drift; those are
  deliberately separate fields.
- `gaps.md`: human-sized list of unique non-uncatalogued gaps, with object
  roles combined. Use the TSV for the full uncatalogued queue.
- `lean_adapter_symbols.tsv`: every literal `Litex.*` symbol emitted by the
  compiler and its exact Rust references.
- `dynamic_lean_adapter_sites.tsv`: every interpolated Lean adapter template
  and its exact compiler sites, selector binding, enclosing function, local
  certificate symbols, and route class. These templates cannot be proved by a
  literal `#check`; each selected value needs a Result-driven generated-module
  tracer.
- `LeanAdapterSymbols.lean`: generated `#check` gate for that literal symbol
  surface. Dynamic theorem-family names are covered by their result tracers,
  not guessed into this file.
- `lean_adapter_gate_evidence.json`: hash-bound real-Lean result for the
  generated symbol gate, with the explicit boundary that a declared name is
  not yet a verified rule-ID/certificate route. The gate is invalidated by any
  imported Lean dependency change, even when its generated `#check` text is
  unchanged.
- `integration_failure_families.tsv`: the current 20-test integration failure
  baseline split into kernel-checked expectation drift, checked-in generated
  drift, and genuine compiler gaps, with one next gate per test.
- `integration_test_inventory.tsv`: all 76 integration tests reconciled to 55
  passing regression gates and the 21 classified failures, with source lines,
  ownership, and one next gate per row.
- `integration_compiler_gap_queue.tsv`: the six genuine red routes split into
  three mechanical `UD-1` handoff slices and three `UD-2` carrier-decision
  slices, each with retained evidence and a negative boundary.
- `example_trust_boundaries.tsv`: all 69 checked pairs classified as 63
  trust-free positives or six explicit source-declared trust boundaries;
  checked Lean axioms without a matching source boundary fail the audit.
- `integration_gate_evidence.json`: Rust-source, test-source, test-binary, and
  failure-ledger hashes for the broad 76-test baseline. A stable Cargo binding
  is retained historically and marked invalid as soon as later Rust sources
  change.
- `runtime_gap_correlations.md`: the five registered compiler failures plus
  three generated-Lean failures mapped to their exact Result/renderer boundary
  and smallest repair gate.
- `example_kernel_matrix.json`: per registered example, hash-bound compiler,
  generated-module kernel, checked-in-module kernel, and drift results from the
  non-destructive all-example gate.
- `example_matrix_baseline.md`: interpretation of the latest matrix, including
  the exact point where a concurrent missing-olean event makes later kernel
  rows infrastructure failures rather than semantic rejections.

## Interpretation boundaries

- `mapped_not_kernel_checked` means current compiler source names the identity.
  It does not replace a `.lit/.lean` tracer and real Lean kernel result.
- An explicit entry in the compiler's fail-closed limitation audit overrides a
  mere source mention; those typed identities remain `evidence_gap` or
  `abi_decision` until their stated boundary is removed and kernel-tested.
- A tracer may be `kernel_checked` while
  `generated_output_matches_checked_in` is false: that means both tested Lean
  artifacts are accepted but regeneration drift still has to be reconciled.
- `evidence_gap` on an uncatalogued builtin means the verifier currently
  returns only the generic uncatalogued identity at this boundary. The
  mechanism classification describes the likely migration family; it is not a
  substitute for reviewing the exact Result children.
- `producer_references`, `compiler_consumers`, and `observer_references` are
  distinct. JSON/graph/LaTeX renderers can prove that an identity is observed,
  but they cannot prove that the verifier constructs it.
- `unreachable` means the extractor found no production source reference at
  this baseline. It is a review target, not proof that no dynamic construction
  can exist.
- Object rows are repeated by occurrence role. A base object lowering does not
  prove that binders, target sets, definitions, function signatures, and WD
  replay all support the same source shape.
- WD artifacts distinguish `direct_source_reference` from
  `enclosing_wd_type:<parent>` consumption. The latter means a compiler-owned
  parent Result contains the artifact; it still needs a focused execution
  tracer before kernel coverage can be claimed.
- Generated rows never authorize a guessed Lean carrier, theorem search,
  `sorry`, an implicit axiom, or the retired universal-object ABI.

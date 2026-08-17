# Compiler2 examples

This directory is the canonical generated ledger for examples targeting the
`litex_to_lean_compiler2` ABI. Every example has one authoritative `.lit`
source and one same-name generated `.lean` output. It must not import or depend
on the archived universal-`Litex.Object` ABI.

Refresh every pair from fresh Litex verification and verifier-owned IR:

```sh
cd lean
./compiler2.sh generate examples
```

After editing one source, refresh only its same-name output:

```sh
cd lean
./compiler2.sh compile examples/1_SetSystem.lit
```

Check byte-for-byte freshness and run every output through Lean:

```sh
cd lean
./compiler2.sh check examples
```

Compiler2 preserves source sketch scope. A top-level `sketch:` becomes an
isolated `__SketchNN` namespace nested inside the file namespace; declarations
and FactIds created there do not become later file-level bindings. Ordinary
top-level facts are emitted directly in the file namespace.

`1_SetSystem.lit` is the tracer for checked named set aliases, `Same`, and
heterogeneous `In`: `have A set = R` becomes an `abbrev A : Litex.Set`, while
verifier equality-rewrite evidence becomes a `Litex.In.congr` proof. A bare
`have A set` remains outside this slice because the verifier has no checked
inhabited-type backend for that arbitrary choice.

`2_OrderSystem.lit` is the tracer for heterogeneous `Lt`/`Le`. Compiler2 emits
`Litex.Lt.toLe` only after validating the registered rule ID, fingerprint,
parameter evidence, and premise evidence.

`3_AtomicEquality.lit` is the first tracer with ordinary top-level facts rather
than a `sketch`. It maps numeric equality to `Litex.Same`, consumes
`ObjectReflexivity` or checked rational-normalization proof IR, and replays the
captured closed-numeric WD membership facts inside the generated theorem.

`4_FunctionSet.lit` is the first unary function-set tracer. Set parameters are
emitted as `Litex.Set` values, while `x` and `f` retain independent carriers
and explicit `Litex.In` hypotheses. Every generated `Litex.fnApply` consumes
the verifier-selected function-membership FactId proof and argument-membership
WD proof. The source `forall` is deliberately top-level rather than wrapped in
`sketch`, so its generated theorem is also file-level. Anonymous functions,
multiple arguments, domain clauses, and curried returns remain outside this
first adapter.

Generated `.lean` files are review artifacts, not editing surfaces. A new
compiler2 feature must add the next numbered same-name pair. Unsupported
statements, objects, facts, or proof routes fail closed.

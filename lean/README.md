# Litex Lean library

This Lake package owns the shared target ABI used by Litex-to-Lean output.

- `Litex.Core` defines the universal `Litex.Object` ABI and its small semantic
  boundary.
- `Litex.Rules` proves concrete verifier rules once and re-exports the
  core by importing it.
- `Litex` is the package root and re-exports `Litex.Rules`.
- [`SEMANTIC_REFERENCE.md`](SEMANTIC_REFERENCE.md) audits every current core
  declaration and builtin theorem against Tao's *Analysis I*, or explicitly
  classifies it as a target representation device, extension, or known drift.

Generated files import only `Litex.Rules`. A generated ABI-version
check fails if the file is compiled against an incompatible shared library.

The executable compiler ledger lives in [`examples/`](examples/). Its
`compile_to_lean_examples.lit` source and checked-in generated
`compile_to_lean_examples.lean` stay beside this ABI and share this Lake
project and toolchain.

## Why the ABI has one object type

The universal `Litex.Object` is not a convenience erasure of native Lean
types. It reflects Litex's pure-set object model: every source value, standard
numeric set, user set, function space, and function value is one object, and
`Litex.In x S` records membership without changing the type of `x`. In
particular, `Litex.N`, `Litex.R`, and `Litex.C` are objects rather than Lean
carrier types, and one numeral object may have membership proofs for all three.

`Litex.Object : Type` is a Lean meta-level carrier, not an internal Litex
universal set. The ABI does not provide unrestricted comprehension, and
partial source constructions are accepted only after the Litex verifier has
retained their exact well-definedness evidence. Object denotation is
proof-free; generated theorems replay that evidence as local propositions in
the Lean scope corresponding to the owning Litex environment. The source
semantics decide that `IsSet` is always true, definitionally, rather than
introducing a second object ontology.

See the [language-level explanation](../docs/Manual.md#pure-set-object-model)
and the
[normative target design](../src/compile_to_lean/litex_object_design.md#why-this-is-source-semantics-not-target-side-type-erasure).

The package is stable within a matching Litex release, not immutable forever.
An incompatible source-semantic or Lean-signature change must be coordinated
with the compiler and reviewed for an `abiVersion` update. Generated files only
import `Litex.Rules`; they do not add a per-file ABI assertion.

Add this package as a Lake dependency before compiling generated output:

```toml
[[require]]
name = "litex"
git = "https://github.com/litexlang/golitex"
rev = "<matching Litex release or commit>"
subDir = "lean"
```

The package currently targets Lean and Mathlib `v4.28.0`.

## Cursor and VS Code

The repository-level workspace enables automatic dependency builds for the
Lean extension. Files below `lean/` use this directory as their Lake project
root and the version in `lean-toolchain`; do not run them as standalone files
from the Rust repository root. A command-line equivalent of the editor check
is:

```bash
cd lean
lake build
```

After dependencies or `lean-toolchain` change, run `Lean 4: Restart Server` in
Cursor once to discard diagnostics produced by the old server process.

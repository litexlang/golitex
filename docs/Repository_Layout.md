# Repository layout and ownership

Litex uses directory boundaries to separate the executable language, its
verification contracts, generated publication material, and long-running
mathematics workspaces. A path must have exactly one Git owner. A nested Git
repository is not a directory-organizing mechanism by itself: it must either
be a registered submodule or be explicitly local-only.

## Root repository

The root `golitex` repository owns the language product:

| Path | Responsibility | Policy |
| --- | --- | --- |
| `src/` | Rust implementation shipped in the crate | Production code only; repository-level tests do not live here. |
| `tests/` | Public integration contracts and private kernel contract sources | Black-box targets use `litex::api`; crate-private white-box tests are loaded explicitly by `src/lib.rs`. |
| `std/` | Builtin Litex standard library | Versioned with the verifier behavior that consumes it. |
| `examples/` | Small executable language examples | Publication-ready examples, not long-lived translation workspaces. |
| `lean/` | Lean ABI, generated compiler pairs, and Lean kernel gates | Root-owned companion source; it must not contain a second `.git` directory. |
| `textbooks/` | Generated publication mirror | Never the canonical editing location. Canonical textbook modules belong to workspaces. |
| `showcases/` | Curated product demonstrations | Versioned only when they are part of the root release surface. |
| `scripts/` | Translation and dataset workspaces | Separate Git owner; see the subrepository contract below. |
| `plan/` | Local planning history | Intentionally absent from the root repository and ignored unless it is promoted to public documentation. |

The public Rust embedding surface is `litex::api`. Existing module paths may
remain for compatibility, but new consumers should not depend on the crate's
internal prelude or on subsystem implementation modules.

## Rust source organization

The number of Rust files is not the primary metric. Each file should have one
recognizable responsibility, and each directory should expose a small module
boundary. Prefer these rules:

1. `src/lib.rs` declares product-level subsystems and the curated API; it does
   not enumerate repository tests.
2. Stateful coordinators keep their lifecycle and dispatch in the parent
   module. Large parsing, rendering, verification, or compilation families are
   private child modules grouped by responsibility.
3. A type is owned by the subsystem that controls its lifecycle. Run-wide
   identity stays run-wide; module loading stays in the module manager;
   environment facts and proof-search state stay in the environment.
4. Cross-subsystem use goes through explicit facade methods or domain types.
   Glob imports remain an internal repository convention, not the public API.
5. Tests are classified by the boundary they assert:
   - black-box behavior uses a normal integration-test crate;
   - white-box kernel contracts live below `tests/kernel_contracts/` and are
     loaded privately under `cfg(test)`;
   - generated or external fixtures stay beside the subsystem that owns their
     generation contract, not beside arbitrary Rust call sites.

## Translation-workspace repository

The `scripts` repository owns canonical textbook translations, dataset
conversion work, proof journals, and their workspace tooling. Its durable
layout should converge on:

```text
scripts/
  README.md
  .textbooks
  tooling/                 shared gates, linters, miners, and tests
  workspaces/              canonical Litex-owned translation workspaces
    <source>/
      textbook/            complete publishable Litex module, when applicable
      proof_journals/
      experience/
      todo/
  external/                independently versioned datasets or upstream sources
```

This is a target boundary, not permission to move dirty workspaces
mechanically. Existing paths remain valid until the owning repository migrates
them together with `.textbooks`, publication mappings, scripts, CI, and source
references.

An independently versioned child below `external/` must be one of:

- a registered Git submodule with a `.gitmodules` entry and a cloneable URL;
- a tool-managed checkout excluded by `.gitignore`, with a reproducible fetch
  command and pinned revision in the owning repository; or
- ordinary vendored files owned entirely by `scripts`, with no nested `.git`.

It must never be both a parent-owned tree and an independent repository.

## Git ownership invariants

Every repository change must preserve these invariants:

1. Every index entry with mode `160000` has a matching `.gitmodules` entry.
2. Every registered submodule has a cloneable URL and a documented purpose.
3. A parent repository does not track files below a child repository's root.
4. An ignored independent repository is documented as local-only or has a
   reproducible acquisition command; it is not silently required by release
   tests.
5. Generated mirrors have one documented canonical source and a deterministic
   synchronization gate.
6. Dirty child repositories are committed, stashed by their owner, or copied
   to an explicitly approved recovery location before topology changes.
7. Removing a nested `.git`, changing a gitlink, or rewriting child history is
   a separately reviewed migration step.

Useful ownership checks from a repository root are:

```bash
git ls-files -s
find . -name .git -print -prune
git status --short
```

Interpret them together: a clean parent status does not prove that ignored or
nested repositories are clean.

## Migration order

Repository topology changes follow this order:

1. inventory every nested repository, its parent index ownership, remote,
   revision, branch, and dirty state;
2. preserve all user-owned changes inside each child repository;
3. remove accidental double ownership, beginning with root-owned directories
   that contain stray Git metadata;
4. make every intended gitlink cloneable and register it in `.gitmodules`;
5. migrate workspace paths inside their owning repository and update all
   registries and gates in the same batch;
6. verify a fresh-clone layout as well as the existing working tree.

The migration is complete only when a fresh clone can reproduce every required
repository and every path has one unambiguous owner.

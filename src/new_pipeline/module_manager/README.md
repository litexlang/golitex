# new_pipeline module management

Canonical design for `litex.config` and the global module world.
Implementation may lag; this note is the contract.

## Goal

One **global** mount table for a run. Nesting is by importing modules.
There is no hierarchy keyword, no submodule, no explicit `flatten` field.

Same physical module folder is mounted **once** (normalized path). Local
aliases in nested configs that point at that path **silently merge** into the
existing global entry. Surface names are for config and display; **IR uses
stable indices**.

## Rename (conceptual)

Today’s type is still named `ModuleManager` in code. Target name:

**`GlobalModuleManager`** — the single owner of current exports and all
imports for the session/project run.

Do not nest a full manager inside each import.

## `litex.config` (import / export only)

### `[export]`

Ordered. Each entry is one `.lit` file only.

```ini
[export]
chap1 = "./chapter01.lit"
chap2 = "./chapter02.lit"
```

### `[import]`

```ini
[import]
Algebra = "../Algebra"
```

### `[import std]`

Same runtime mount as `[import]` after path resolve. Two spellings:

```ini
[import std]
basics
basics = basics
myB = basics
```

- bare `N` means `N = N`
- `Alias = StdName` → `<std_root>/<StdName>` under `Alias`

Hand-written std paths under ordinary `[import]` are deferred.

### Alias / export name clash at one config layer (tightened)

Within one `litex.config`:

1. Aliases from `[import]` and `[import std]` share one namespace and must
   not collide with each other.
2. An import alias must **not** reuse a name from that same file’s
   `[export]` table (and conversely). This keeps two-segment `a::b`
   unambiguous even with single-export fill-in sugar.
3. Manifest sections are always **imports first, then exports** (run and
   elaborate assume imports are already on the global table before that
   module’s export files run).

Across nested configs, the same path may use different aliases; see
**path dedup / silent merge** below (not a clash — a remapping to one `m_i`).

## Global shape (target)

```text
GlobalModuleManager
  current_exports: Vec<ExportFileAndItsExecEnv>
      # the module currently being run; ordered; does NOT occupy an m_i
  imports: Vec<ImportedModule>
      # every mounted module in the project world (including transitive)
```

```text
ImportedModule
  name: String           # preferred global display alias (first registration wins)
  path: PathBuf          # normalized path; dedup key
  litex_config: ...      # recorded manifest of that module
  export_files_and_their_env: Vec<ExportFileAndItsExecEnv>
  # NO nested ModuleManager / NO per-import import subtree
```

### Transitive imports and readiness (no circular import)

Imports are recorded on the **global** table (by path), not left in a
per-module import subtree.

**Readiness rule (locked):** before module `A` may be mounted / run, every
module that `A`’s own `[import]` / `[import std]` names must **already** be
present on the global import table (same path → already merged as some
`m_i`). `A` must not be the first place that introduces a still-missing
dependency.

Under this rule a cycle `A ↔ B` cannot succeed: neither can become ready
while waiting for the other to be on global first. Implementation-wise it is
enough to check “dep path already in `imports` (and ready)” when entering
`A`; a separate fancy cycle graph is unnecessary if this check is always
applied.

Typical outer setup: the root (or earlier mounts) registers `B` before `A`
is entered; `A`’s local alias for `B` only remaps to the existing `m_i`.

### Path dedup / silent merge (locked)

Dedup key: **normalized directory path**. Same folder → at most one
`ImportedModule` / one `m_i`.

Example:

- Global config: `G = "../Foo"` → register `m1`, display name `G`
- Nested config of `A`: `T = "../Foo"` (same path)
  - do **not** mount again
  - local name `T` means “the existing `m1`”
  - while running in the global world, identity is `m1`; display may prefer `G`

This is why an **internal representation** is required: local alias ≠ identity.

### Ordering

- **`[export]` order matters** (run order / prefix).
- **`[import]` order need not define identity.** Loading may still schedule
  “ensure dependency mounted before running a module’s exports,” but imports
  are not a second ordered world inside each `ImportedModule`.

### Root / current module

The outermost root does not take an `m_i` slot. When elaborating `a::b`,
step 1 looks at the `[export]` table of the module that owns the `.lit`
file currently being run (only one file runs at a time).

## Internal IR vs display (locked)

| Layer | Module | Export file inside a module |
|---|---|---|
| Display / config | `G`, `basics`, … | `chap1`, `main`, … |
| IR | `m1`, `m2`, … (registration index in `imports`) | `f1`, `f2`, … (index in that module’s `[export]` order) |

Parse / elaborate maps surface quals into IR. Display maps IR back.

Examples (after elaborate):

- `G::chap1::x` → `m1::f2::x` (indices illustrative)
- single-export sugar: `basics::x` → fill only export → then `m_k::f1::x`

## Two-segment name `a::b` (parse vs global table)

When elaborating `a::b`:

1. If `a` is a name in **current** `[export]` → `current f_* :: b` (no fill).
2. Else `a` must resolve to some import alias (possibly after local→`m_i` map).
   - that `ImportedModule` has **exactly one** export → treat as
     `a::<that export>::b` then to `m_i::f1::b`
   - zero or more than one export → two-segment form is illegal; require
     `a::export::b`

Three-segment `a::b::c` is always import-alias / `m_i` + export/`f_j` + name.
Explicit three-segment form remains allowed when single-export sugar also
applies.

No fourth segment (no submodule).

## Runtime sameness of std

| Config | After resolve | Global table |
|---|---|---|
| `[import] Alias = path` | module at `path` | one `ImportedModule` (or merge by path) |
| `[import std] N` | `N = N` | same |
| `[import std] Alias = StdName` | `<std_root>/StdName` | same |

## Code debt vs this note

Current code may still have nested `ModuleManager` inside imports and the
old type name. Treat that as lagging implementation. Changing the Rust
structs requires an explicit Core Struct approval when editing.

## Explicit non-goals / deferred

- Config parser and `-r` / project `-f` wiring
- Ordinary `[import]` of a hand-written std filesystem path
- Explicit `flatten` / `[hierarchy]` / `submodule`

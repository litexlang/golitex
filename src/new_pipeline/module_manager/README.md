# new_pipeline module management

Design target for `new_pipeline` module loading and `litex.config`.

## Goal

One flat composition unit: a **module** (directory with `litex.config`).
Nesting is by **importing modules**. No hierarchy keyword, no submodule, no
flatten in this design.

## `litex.config` (import / export only)

A module manifest has two user-facing tables for now:

### `[export]`

Ordered explicit list. Each entry is one `.lit` file only.

```ini
[export]
chap1 = "./chapter01.lit"
chap2 = "./chapter02.lit"
```

Invalid: exporting a folder / nested config node.

### `[import]`

Mount another module directory under an alias.

```ini
[import]
Algebra = "../Algebra"
```

Meaning: alias `Algebra` → that folder (must itself be a module).

### `[import std]`

Syntax sugar for mounting a package under the std root. Same runtime object as
`[import]` after path resolution.

Two spellings when loading `litex.config`:

```ini
[import std]
basics
basics = basics
myB = basics
```

- **no `=`:** a bare name `N` means `N = N` (left alias equals right package name).
- **with `=`:** `Alias = StdName` as usual.

Resolution rule (locked):

- after normalizing the no-`=` form, always `Alias = StdName`
- mount path is always `<std_root>/<StdName>`
- examples: `basics` or `basics = basics` → `<std_root>/basics` as `basics`;
  `myB = basics` → `<std_root>/basics` as `myB`

Not in scope for now: writing a literal std path under ordinary `[import]`
(e.g. `basics = "/.../std/basics"`). That would be equivalent in principle, but
is not supported yet.

### Full example

```ini
[import]
Algebra = "../Algebra"

[import std]
basics
basics = basics

[export]
chap1 = "./chapter01.lit"
chap2 = "./chapter02.lit"
chap3 = "./chapter03.lit"
```

### Alias uniqueness

`[import]` and `[import std]` share **one** alias namespace.

These two aliases must not collide (config error / `record_import` error):

```ini
[import]
basics = "../OtherBasics"

[import std]
basics = basics
```

Canonical cites use the alias, e.g. `Algebra::chap1::name`, `basics::name`,
`myB::name`.

## Runtime sameness

| Config section | After resolve | In `ModuleManager` |
|---|---|---|
| `[import] Alias = path` | module at `path` | `ImportedModule { name: Alias, path, ... }` |
| `[import std] N` | same as `N = N` | same `ImportedModule` shape |
| `[import std] Alias = StdName` | module at `<std_root>/StdName` | same `ImportedModule` shape |

There is no separate `import_std` store.

## Ownership in `ModuleManager`

```text
ModuleManager
  export_files_and_their_env: Vec<ExportFileAndItsExecEnv>
  imports: Vec<ImportedModule>   # [import] + [import std]
```

- `ImportedModule`: `name` (alias), `path` (resolved), `module_manager`
- `record_import` rejects duplicate aliases
- completed envs stay on the node that executed them; imports are not merged
  into the importer’s export list

## Explicit non-goals / deferred

- No `submodule`, no `[hierarchy]`, no `flatten`
- No `-r` / project `-f` wiring yet
- No importing a single `.lit` as a package
- No ordinary `[import]` of a hand-written std filesystem path yet
- Config parser / discovery implementation may follow this note later

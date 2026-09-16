# new_pipeline module management — final data plan

Canonical contract. Implementation may lag; further Rust renames need Core
Struct / AST approval when coding.

## Package layout (`src/new_pipeline/module_manager/`)

| File | Owns |
|------|------|
| `global_module_manager.rs` | `GlobalModuleManager`, `path_to_mod_id`, `current_mod_id`, record APIs |
| `imported_module.rs` | `ImportedModule` |
| `export_file.rs` | `ExportFileAndItsExecEnv` |
| `litex_config.rs` | `LitexConfig` + import/export rows |
| `parse_litex_config.rs` | parse `[import]` / `[import std]` / `[export]` |
| `mount.rs` | `set_root_config` / `ensure_imports_ready` / `mount_module` (no `.lit` run) |
| `elaborate_name.rs` | `::` / `:::` → id-based `AtomicName` |
| `README.md` | this contract |

`Runtime.global_module_manager` holds the single `GlobalModuleManager` for a
run. **`-r` / project `-f` execution is out of scope** for this package’s
current work; only tables + parse + name elaborate live here.

## Name forms (syntax)

| Form | Meaning after elaborate |
|------|-------------------------|
| `x` | local / current-module plain name |
| `a::b` | current module export file `a`, symbol `b` → `WithMod { file_id, name }` |
| `a::b::c` | import alias `a` → global module, export `b`, symbol `c` → `WithModAndExport` |
| `a:::b` | flatten sugar only → sole export `F` → same as `a::F::b` |

- No `[hierarchy]`, no `submodule`, no config `flatten`.
- Export name may equal an import alias; forms disambiguate.
- Import aliases within one config must not collide with each other.
- Imports before exports. Deps of a module must already be on global before it runs.

---

## Data structures and what each is for

### `GlobalModuleManager` (session / project owner)

One per run. Not nested inside imports.

| Field | Type | Purpose |
|-------|------|---------|
| `litex_config` | `LitexConfig` | Root module’s parsed `litex.config`. |
| `root_exports` | `Vec<ExportFileAndItsExecEnv>` | Root’s ordered completed export files + envs. Root is **not** an `imports` slot / not a `mod_id`. |
| `imports` | `Vec<ImportedModule>` | Global mount table. **Index = `mod_id`**. Display global name = `imports[mod_id].name`. |
| `path_to_mod_id` | `HashMap<PathBuf, usize>` | Normalized module dir path → `mod_id`. Dedup + resolve: local alias → path → `mod_id`. First registration wins; silent merge does not overwrite. |
| `current_mod_id` | `Option<usize>` | `None` = not inside an imported module (root / -e / REPL); `Some(i)` = currently parsing/running `imports[i]`. |

No `HashMap<mod_id, name>`: name is `imports[mod_id].name`. Missing / bad id → error (deps must be ready).

**API sketch:** `record_import` by path (merge or push); `record_root_export`; lookup `path_to_mod_id`.

---

### `ImportedModule` (one global mount)

| Field | Type | Purpose |
|-------|------|---------|
| `name` | `String` | Preferred global alias (first registration). |
| `path` | `PathBuf` | Normalized dir; same as key in `path_to_mod_id`. |
| `litex_config` | `LitexConfig` | That folder’s manifest (for its own imports/exports when running its files). |
| `export_files_and_their_env` | `Vec<ExportFileAndItsExecEnv>` | That module’s ordered exports + envs. **Index = `file_id`** inside this module. |

No nested manager. No per-module alias→global map: use `litex_config.imports` (alias→path) + global `path_to_mod_id`.

---

### `ExportFileAndItsExecEnv`

| Field | Type | Purpose |
|-------|------|---------|
| `name` | `String` | Config export name (display; `file_id` → this when displaying). |
| `path` | `PathBuf` | `.lit` path. |
| `exec_env` | `Box<ExecEnv>` | Top-level env after that file finished. |

Used in `root_exports` and in each `ImportedModule.export_files_and_their_env`.

---

### `LitexConfig` (config AST only; rows not separate public types)

| Field | Type | Purpose |
|-------|------|---------|
| `imports` | `Vec<{ alias, path }>` | Resolved mounts: relative path or `<std_root>/<StdName>`. Bare `[import std] N` ⇒ `N = N`. |
| `exports` | `Vec<{ name, path }>` | Ordered `.lit` only. |

Root and every `ImportedModule` each own one.

---

### `AtomicName` (qualified atom identity; keep this name — do **not** reuse binder `Identifier`)

Replace string `mod_name` / `export_name` with ids after elaborate:

| Variant | Fields | Purpose |
|---------|--------|---------|
| `Plain` | `name: String` | Unqualified atom. |
| `WithMod` | `file_id: usize`, `name: String` | `a::b` in **current** module: export index + symbol. |
| `WithModAndExport` | `mod_id: usize`, `file_id: usize`, `name: String` | Cross-module ref: global import index + that module’s export index + symbol. |

- Identity of qualified refs = these ids + `name` (not local alias strings). Same path under `T` vs `G` → same `mod_id`.
- Display: `mod_id` → `imports[mod_id].name`; `file_id` → that module’s (or root’s) `exports[file_id].name`.
- `ModuleId` / `ExportFileId` newtypes: deferred; `usize` is enough.

Binder plain names stay the existing AST `Identifier` / `PlainName` — unchanged by this plan.

---

## Resolve cheat-sheet (one file running at a time)

Current module = owner of the running `.lit`.

```text
a::b
  → file_id = index of export "a" in *current* export list
  → AtomicName::WithMod { file_id, name: b }

a:::b
  → alias a in current LitexConfig.imports → path
  → mod_id = path_to_mod_id[path]          # must exist
  → that ImportedModule must have exactly one export F
  → same as a::F::b → WithModAndExport { mod_id, file_id: 0, name: b }

a::b::c
  → alias a → path → mod_id = path_to_mod_id[path]
  → file_id = index of export "b" in imports[mod_id].exports / export_files
  → WithModAndExport { mod_id, file_id, name: c }
```

---

## Implementation phases

| Phase | Work |
|-------|------|
| **0** | ✅ `GlobalModuleManager` package; flatten `ImportedModule`; `path_to_mod_id`. |
| **1** | ✅ Parse `LitexConfig` (`[import]` / `[import std]` / `[export]`). |
| **2** | ✅ Mount + readiness **table** APIs (`mount_module` / `ensure_imports_ready`); no `.lit` execution. |
| **3** | ✅ Id-based `AtomicName` + `::` / `:::` elaborate. |
| **4** | Deferred: wire `-r` / project `-f` (explicitly not in this pass). |

---

## Explicit non-goals

- Legacy `module_system` / old `ProjectConfig` hierarchy & flatten
- Hand-written std path via ordinary `[import]`
- Extra `mod_id → name` HashMap
- Nesting `ModuleManager` inside imports

# new_pipeline `knowledge_base`

Owns **persistence and restore** of imported-module products so `-r` / `-f` /
`-e` / REPL preload can skip repeating `exec_stmt` on clean dependency trees.

This package is an **accelerator**. It must not change proof routes or
mathematical results. A cache hit must leave the session looking like a full
cold `run_import_module` of the same module.

Companion packages:

| Package | Owns |
|---------|------|
| `module_manager/` | Live tables: `ImportedModule`, `ExportFileAndItsExecEnv`, mount APIs |
| `run_module/` | Cold path: recurse imports, run export `.lit`, record envs |
| `knowledge_base/` (this) | Fingerprint, serialize/deserialize, load + id/`mod_id` remap, write-back |
| `runtime/` / `exec_env/` | Session owners that load must remount into (authorization-gated) |

## Package layout (implemented so far)

| File | Owns |
|------|------|
| `mod.rs` | Module exports only |
| `json_mini.rs` | Zero-dep JSON `Value` + parse/stringify |
| `def_prop_codec.rs` | Store/load one `DefPropStmt` as JSON |
| `README.md` | This contract |

White-box tests live under
`tests/unit/new_pipeline/knowledge_base/` (see that folder’s README), loaded by
`#[cfg(test)]` from this `mod.rs`. **Human-facing goldens and `.lit` sources**
live under `examples/new_pipeline/knowledge_base/` (def_prop first).

Public API (def prop only for now):

| Fn | Role |
|----|------|
| `store_def_prop` / `load_def_prop` | `DefPropStmt` ↔ JSON `String` |
| `write_def_prop` / `read_def_prop` | same ↔ file on disk |

Implementation may lag later sections. Wiring into `run_import_module` comes
after format / fingerprint / remap contracts are fixed.

---

## DefPropStmt wire format (first codec)

**Decision locked:** store a full elaborated `DefPropStmt` AST snapshot (not
source text, not a FactId-stripped DTO). Hand-written codec in
`knowledge_base` (no `serde` on AST structs).

### Flow

```text
cold exec_def_prop
  → ExecEnv.definitions.predicate_definitions[name] = DefPropStmt
  → store_def_prop / write_def_prop  →  JSON text or file

later
  → load_def_prop / read_def_prop  →  DefPropStmt
  → (future) GlobalIds + global_mod_id remap
  → insert predicate_definitions[name]
```

Map key stays **plain** `name` (e.g. `is_pos`). Qualified `M::F::is_pos` is
built at cite time from mount ids + this plain name.

### Example source

```litex
prop is_pos(x R):
    x > 0
```

### Example JSON (shape; ids illustrative)

```json
{
  "kind": "def_prop",
  "name": "is_pos",
  "typed_parameters": {
    "groups": [
      {
        "params": [{ "id": 7, "name": "x" }],
        "param_type": {
          "tag": "Obj",
          "obj": { "tag": "StandardSet", "set": "R" }
        }
      }
    ]
  },
  "iff_facts": [
    {
      "tag": "AtomicFact",
      "atomic": {
        "tag": "GreaterFact",
        "fact_id": 42,
        "left": {
          "tag": "Identifier",
          "identifier": { "tag": "Plain", "id": 7, "name": "x" }
        },
        "right": {
          "tag": "Literal",
          "literal": { "tag": "Number", "text": "0" }
        },
        "line_file": null
      }
    }
  ],
  "line_file": {
    "line": 1,
    "origin": {
      "export_file_id": 0,
      "tag": "RootExport"
    }
  }
}
```

`line_file` is a `SourceLine`: line number plus `CodeSource` origin (no absolute
path). `StandaloneFile` / display paths live on `Runtime.current_file`.

### Supported AST subset (grow over time)

| Area | Supported now |
|------|----------------|
| `ParamType` | `Set` / `NonemptySet` / `FiniteSet` / `Obj` |
| `Obj` | `Identifier` (all three forms), `Literal` (Number/i/e/pi), `StandardSet` |
| `Fact` | `AtomicFact` only |
| `AtomicFact` | order/equality compares + `In` / `NotIn` (and their `Not*` compare forms) |

Other `Obj` / `Fact` variants → `KbCodecError::Unsupported`. Expand the codec
when real props need them; do not silently drop fields.

### Acceptance

Unit tests in `def_prop_codec.rs`: `is_pos`-shaped `DefPropStmt` →
`store_def_prop` → `load_def_prop` → `PartialEq`; plus temp-file
`write_def_prop` / `read_def_prop`.

---

## What `__litex_knowledge_base__` is for (on-disk artifact)

`__litex_knowledge_base__/` is a **local, gitignored build artifact directory**
placed beside a module’s `litex.config` (same idea as `__pycache__` / `target/`).

| | |
|--|--|
| **Who writes it** | Litex, after successfully building that import module |
| **Who reads it** | Later `-r` / import of the same module, when fingerprint is still valid |
| **What it stores** | The module product: finished export envs (and manifest / fingerprint), not raw `.lit` text as the source of truth |
| **What it is not** | Not a proof library users edit by hand; not a substitute for sources; not allowed to change math when hit |

Sources + `litex.config` remain authoritative. If anything in the fingerprint
set changes (or the KB ABI / kernel contract bumps), the artifact is ignored
and the module is rebuilt, then the directory is updated again.

Exact file names inside `__litex_knowledge_base__/` (e.g. binary blob vs JSON
projection) are still design-open; this README only fixes the **role** of the
directory versus this Rust package.

---

## Observation: what importers actually read from a finished export env

Why store an import module’s `ExecEnv` at all? So **other** modules that
`import` it can resolve `M::F::…` without re-running that package.

**Consumer contract (current `new_pipeline` lookup paths):**

| Used across finished export envs? | What |
|-----------------------------------|------|
| **Yes** | `definitions` — especially `theorem_definitions`, `predicate_definitions`, `abstract_predicate_definitions`, and `identifiers` (release / expand-by-def) |
| **No** | `facts` (known-fact indexes / `facts_by_id` search) |
| **No** | `well_defined_objects` as a cross-module known-WD library |
| **No** | `prop_rewrite_properties` / most `special_object_properties` walks (those stay on the **live** exec-env stack) |

Code anchors: qualified def lookup and release go through
`finished_export_exec_env` → `definitions` (`env_stack_lookup`,
`execute_release_obj_def_stmt/lookup`). Known-fact / WD / rewrite searches
iterate `execution_environments_stack` only.

So for an **importer**:

- Read defs, release object defs, apply thms / props from the imported package’s
  definition memory.
- Applying a thm means: take the `DefThmStmt`, instantiate and discharge
  premises in **this** session, store conclusions in **this** live env — not
  cite the foreign env’s old `FactId`s as known facts.
- Qualified identifiers are treated as already-resolved for object WD; the
  importer does not mine the foreign WD table.

Known facts inside an export env matter when **building that file** (and for
a full cold-run isomorphic product). They are **not** the API surface for
later `import` consumers.

**lkb implication:** the *motivation* for caching import products is this
definition / release / thm surface. MVP still prefers storing a full
`ExecEnv` per export so a cache hit matches cold `run_import_module`
shape; definitions-only blobs remain a possible later optimization if this
consumer contract is frozen and measured.

---

## Locked: when to read / rebuild / write (pycache rhythm)

Same **frequency model** as Python `__pycache__`: check on import (and on
`-r` while building deps); miss or stale → rebuild; success → write back.
Difference from CPython: **staleness is content-addressed**, not mtime-only.

### Write-back (update / create `__litex_knowledge_base__`)

| Rule | |
|------|--|
| **When** | Every time an **imported** module is **successfully** built in-session |
| **Paths** | `-r` via `run_import_module`, and `-f` / `-e` / REPL import preload that cold-runs or dirty-rebuilds the same |
| **Create** | No lkb dir / artifact yet → write after success |
| **Overwrite** | Artifact existed but this run rebuilt the module → replace with the new product |
| **Do not write** | Cache **hit** (load only); soft Fail / FailToImport / SessionError; partial export failure |

MVP: write for **imported packages** only. Root’s own exports stay cold-run
each time unless a later decision extends caching.

### Dirty / must rebuild (not mtime-alone)

| Rule | |
|------|--|
| **Authority** | Content-addressed **fingerprint** (this module’s `.lit` + `litex.config`, transitive deps, std, Litex kernel / KB ABI) |
| **Hit** | Fingerprint matches → load + remap; skip re-`exec_stmt` for that module’s exports |
| **Miss** | Missing artifact, fingerprint mismatch, or unloadable/corrupt → cold `run_import_module` for that module, then write-back on success |
| **mtime** | Optional fast reject only; **never** the sole validity check |

Mental loop:

```text
import / -r reaches module M
  → fingerprint(M) vs lkb?
      match → load
      else  → run exports → on success write/update lkb
```

---

## Locked: load remap (session view → new Runtime)

A stored module product is a **frozen session view** of that import’s finished
export `ExecEnv`s. Loading into another Runtime must make citations and indexes
look as if the module had been cold-built in *this* session.

There are **two semantic remap families** (and no third kind of session index
inside `ExecEnv` today):

### 1. Monotonic `GlobalIds` (uniform per-counter delta)

`ExecEnv` records `global_ids_at_enter` / `global_ids_at_leave`. On load, for
each counter (`FactId`, `WellDefinednessId`, `IdentifierId`, and
`PropRewritePropertyId` if it ever appears in env data):

```text
delta = runtime.now - cached_enter
every id of that kind in the env  += delta
runtime.now  = cached_leave + delta
```

Example: saved enter fact=90, load when runtime fact=100 → add 10 to every
`FactId` in that product; then advance the live counter past the remapped
leave.

Same idea for the other counters; deltas are **per counter**, taken from the
enter/leave snapshots (not one magic number for all kinds).

### 2. `global_mod_id` on qualified names (path-anchored table)

`AtomicName::WithModAndExportFileId` and `IdentifierObj::WithModAndExportFileId`
carry a **this-run** `global_mod_id`. Numbers are not stable across sessions.

On load, remap with a table built from **module path** (not “add a constant”):

| In the blob | Meaning | New value |
|-------------|---------|-----------|
| self’s old mod id | this imported module | this session’s `path_to_mod_id[self]` |
| dep’s old mod id | an import that module used | this session’s `path_to_mod_id[dep]` |

Example: saved `m2::f3::T`, now this package is mod 5 → every such occurrence
becomes `m5::f3::T`. A cite that was `m10::…` for a dep that is now mod 8
becomes `m8::…`.

**`export_file_id` does not remap** on a valid load: it is that module’s
`[export]` order. If exports change, the fingerprint must miss and the module
is rebuilt (never load a layout-mismatched blob).

`WithExportFileId` (no mod field) is “current module + export index”; the index
stays; only the mount slot of the whole product changes.

The lkb manifest must therefore store enough to rebuild the old
`mod_id → path` map used when the blob was written (so load can invert to
`old_mod_id → new_mod_id`).

### Implementation note (not a third semantic family)

Plain `IdentifierId` and qualified `mN::fK::…` are embedded in `ObjIR` /
index keys (`#id#name`, `m2::f3::…`). Remap must **rewrite AST and rebuild
`HashMap` keys** (`facts_by_id`, WD maps, `special_object_properties`,
equality-class indexes, …). That is the same two families above, applied
through IR — not a separate kind of stored identity.

# `knowledge_base`

Owns **persistence and restore** of imported-module products so `-r` / `-f` /
`-e` / REPL preload can skip repeating `exec_stmt` on clean dependency trees.

This package is an **accelerator**. It must not change proof routes or
mathematical results. A cache hit must leave the session looking like a full
cold `run_import_module` of the same module (for the **definition / release /
thm** surface consumers actually use).

Companion packages:

| Package | Owns |
|---------|------|
| `module_manager/` | Live tables: `ImportedModule`, `ExportFileAndItsExecEnv`, mount APIs |
| `run_module/` | Cold path + KB hit/write via `import_kb.rs` |
| `knowledge_base/` (this) | Fingerprint, codecs, remap, write/load helpers (`import_cache`) |
| `runtime/` / `exec_env/` | Live session; KB only reads watermarks / installs finished export envs via run_import |

---

## Design locked (summary)

These decisions are fixed for the current MVP. Change them only with an
explicit contract bump (`KB_ABI`) and docs update.

### 1. Role

| | |
|--|--|
| **What** | Local, gitignored build cache beside each imported module’s `litex.config` |
| **Dir name** | `__litex_knowledge_base__/` (pycache rhythm, not mtime-alone) |
| **Authority** | Sources + `litex.config` remain source of truth; KB is never hand-edited math |
| **Scope** | **Imported** modules only (root exports stay cold unless later extended) |

### 2. Product shape (definitions-only)

Importers resolve `M::F::…` through finished export **`definitions`**
(`by def`, `release thm` / `by thm`, `release obj def`, …). They do **not**
mine foreign `facts` / WD / rewrite tables.

Therefore the on-disk MVP stores **per-export `DefinitionMemory`**, not a full
`ExecEnv`. Hit installs an `ExecEnv` whose `definitions` are remapped and whose
facts/WD maps stay empty (same consumer contract as today).

`DefThmStmt.prove_process` is **stripped on write** (empty on load): release /
by thm only need the goal interface.

### 3. On-disk layout

```text
<module_root>/__litex_knowledge_base__/
  manifest.json                 # abi, fingerprint, mod_id↔path, export watermarks
  exports/<export_file_id>/
    definitions.json            # one DefinitionMemory (supported subset)
```

`KB_ABI` (`paths.rs`) bumps when wire/manifest layout is incompatible or a
verifier correction invalidates previously checked products. ABI 3 keeps the
ABI 2 layout, but forces a cold rebuild after exact decimal normalization and
aggregate WD corrections. The old checker could accept a false decimal
inequality; cached theorem interfaces omit their proof process and cannot be
treated as freshly checked by the repaired verifier. The fingerprint includes
the ABI revision and old manifests are rejected, so imports rebuild once and
then use the ordinary cache again. Runtime/Env state shapes are unchanged.

ABI 2 introduced the `HaveFnEqual` statement name as a `BoundName` (`id`, `name`)
and remaps that ID together with the function's parameter/body IDs. ABI 1
module products are cache misses and are rebuilt from source. A standalone
legacy `HaveFnEqual` record with a string name is rejected because it contains
no declaration ID to restore.
JSON string decoding preserves UTF-8 bytes, so module paths and identifier
names containing non-ASCII characters round-trip without changing identity.

### 4. Import hook (always on)

| | |
|--|--|
| **Where** | `run_module/import_kb.rs` (called from `run_import_module`) |
| **Policy helpers** | `knowledge_base/import_cache.rs` (fingerprint, hit, cold write-back) |
| **Gate** | None — every successful import tries hit, then write after cold |

### 5. Load / rebuild / write loop

```text
run_import_module(M):
  recurse deps (same as today)
  mount_module(M) → mod_id
  try_finish_import_from_kb:
    fp = fingerprint(M + transitive import sources + KB_ABI)
    try_hit(fp):
      hit  → remap ids → record finished exports from definitions
             → advance Runtime.global_ids to remapped leave
             → skip cold exec of M's exports; Done
      miss → fall through
  cold: run_export_file for each export (unchanged)
  write_kb_after_cold_import (best-effort;
    Unsupported def shapes → skip / clear cache, do not fail import)
```

Fingerprint is **content-addressed** (stable FNV-1a over config bytes, ordered
export bytes, sorted dep fingerprints, ABI). mtime is never the sole validity
check.

#### How hit is decided

```text
fp_now = fingerprint_module_recursive(M)
read M/__litex_knowledge_base__/manifest.json
  missing / unreadable / abi mismatch     → miss
  manifest.fingerprint != fp_now          → miss   (sources or deps changed)
  export count ≠ litex.config [export]    → miss
  definitions.json unloadable / corrupt   → miss
  otherwise                               → hit → load + remap; skip cold exec
```

One line: **hit = same fingerprint as last successful cold write, and the
cache still loads cleanly.**

Do **not** write on: cache hit; soft Fail / FailToImport / SessionError;
partial export failure.

### 6. Remap on every load (required)

A KB blob is a **frozen session view**. Loading into another Runtime must look
as if M were cold-built **in this session**. Two families only:

**A. GlobalIds (per-counter delta)**

```text
delta_k = runtime.now_k - cached_enter_k
every id of kind k in the product  += delta_k
after each export: cursor = cached_leave + deltas
finally: runtime.global_ids = remapped leave of last export
```

Kinds: `FactId`, `WellDefinednessId`, `PropRewritePropertyId`, `IdentifierId`.
Watermarks in the manifest are **KB-owned u64 snapshots** (`GlobalIdsSnapshot`);
`GlobalIds::to_u64s` / `from_u64s` bridge Runtime without exposing private fields
elsewhere.

**B. `global_mod_id` (path table)**

Manifest stores `old_mod_id → module path`. Load builds
`old_mod_id → new_mod_id` via this session’s `path_to_mod_id`. Rewrite
`WithModAndExportFileId` (and any other mod-carrying cites in the def subset).

**Do not remap `export_file_id`.** It is that module’s `[export]` order; if
exports change, fingerprint must miss and rebuild.

### 7. Outside-KB surface (minimal)

The **only** intentional non-KB call site for the cache policy is
`run_import_module` (plus tiny `GlobalIds` watermark helpers on Runtime).
Do not scatter write/hit logic into `execute/` or `module_manager/`.

### 8. Acceptance

| Test | What it proves |
|------|----------------|
| `knowledge_base::unit_tests::*` | Codecs, fingerprint, write/mount remap |
| `run_module::tests::run_project_kb_cache_write_then_hit_cross_mod` | Cold writes lkb; second `-r` hits; `by def` / `release thm` / `by thm` / `release obj def` still succeed; lib export not re-exec’d |

```bash
cargo test -p litex-lang --lib \
  run_module::tests::run_project_kb_cache_write_then_hit_cross_mod \
  -- --exact
```

### 9. Non-goals / deferred

- Full `ExecEnv` blob (facts, WD, rewrite indexes)
- Caching **root** exports
- Remaining identifier tags (case/induc/exist!, trust, …), template, strategy, algo
- Silent field drops (unsupported → `KbCodecError::Unsupported`)
- User-edited KB as a library

---

## Package layout

| File | Owns |
|------|------|
| `mod.rs` | Module exports only |
| `json_mini.rs` | Zero-dep JSON `Value` + parse/stringify |
| `def_prop_codec.rs` | `DefPropStmt` + shared AST wire helpers |
| `def_abstract_prop_codec.rs` | `DefAbstractPropStmt` |
| `def_thm_codec.rs` | `DefThmStmt` (empty `prove_process` on wire) |
| `stored_identifier_codec.rs` | `StoredIdentifierDefinition` MVP tags |
| `axiom_codec.rs` | `AxiomStmt` |
| `def_struct_codec.rs` | `DefStructStmt` |
| `definitions_memory_codec.rs` | One export’s `DefinitionMemory` subset |
| `fingerprint.rs` | Content-addressed module fingerprint |
| `manifest.rs` | `manifest.json` + `GlobalIdsSnapshot` |
| `remap.rs` | Apply GlobalIds deltas + `global_mod_id` table |
| `mount.rs` | `write_module_kb` / `try_mount_module` |
| `import_cache.rs` | Fingerprint tree, hit helpers, cold write-back, `ExecEnv` from mounted defs |
| `paths.rs` | On-disk paths + `KB_ABI` |
| `README.md` | This contract |

White-box tests: `tests/unit/knowledge_base/` (loaded via
`#[cfg(test)]`). Codec goldens / `.lit` surfaces:
`examples/knowledge_base/`.

### Public API (high level)

| Fn | Role |
|----|------|
| per-kind `store_*` / `load_*` | Single definition codecs |
| `store_definition_memory` / `load_…` | One export `DefinitionMemory` |
| `compute_fingerprint` / `fingerprint_module_recursive` | Cache key |
| `write_module_kb` / `try_mount_module` | Disk write / load+remap |
| `try_hit_import_cache` / `write_import_cache_after_cold` | Import cache helpers |
| `exec_env_from_mounted_export` | Build finished-export `ExecEnv` for record |
| `remap_definition_memory` / `RemapPlan` | Id rewrite |

### Codec roadmap

| Priority | Kind | Status |
|----------|------|--------|
| 1–6 | prop / abstract_prop / thm / identifiers / axiom / struct | done (see subset limits) |
| 7 | mount + import hook | done (always on) |
| next | more have-fn tags; template; fuller Obj/Fact; optional full ExecEnv | planned |

---

## Import hook (detail)

KB load/write is always attempted for imported modules.

```text
import M
  → recurse deps
  → mount_module
  → fingerprint + try_hit_import_cache
       hit  → install remapped DefinitionMemory into finished exports; skip exec
       miss → cold run_export_file… → write_import_cache_after_cold (best-effort)
```

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
  → GlobalIds + global_mod_id remap (on mount)
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
| `Obj` | `Identifier` (all three forms), `Literal` (Number/i/e/pi), `StandardSet`, `FnSet`, `AnonymousFn`, arithmetic `Add`/`Sub`/`Mul`/`Div`/`Neg` |
| `Fact` | `AtomicFact`, `ForallFact` (then-clause: atomic only for now) |
| `AtomicFact` | order/equality compares + `In` / `NotIn` (and their `Not*` compare forms) |
| `QuantifierFreeFact` | atomic (for FnSet / set-bound dom) |

Other `Obj` / `Fact` variants → `KbCodecError::Unsupported`. Expand the codec
when real props need them; do not silently drop fields.

### Acceptance

Unit tests under `tests/unit/knowledge_base/`: round-trip +
example goldens; `LITEX_DUMP_KB_FIXTURES=1` regenerates goldens.

---

## What `__litex_knowledge_base__` is for (on-disk artifact)

`__litex_knowledge_base__/` is a **local, gitignored build artifact directory**
placed beside a module’s `litex.config` (same idea as `__pycache__` / `target/`).

| | |
|--|--|
| **Who writes it** | Litex, after successfully building that import module (when cache enabled) |
| **Who reads it** | Later `-r` / import of the same module, when fingerprint still matches |
| **What it stores** | Manifest + per-export **definitions** (MVP); not raw `.lit` as source of truth |
| **What it is not** | Not a proof library users edit by hand; not a substitute for sources; not allowed to change math when hit |

Sources + `litex.config` remain authoritative. If anything in the fingerprint
set changes (or `KB_ABI` bumps), the artifact is ignored and the module is
rebuilt, then the directory is updated again.

---

## Observation: what importers actually read from a finished export env

Why cache an import module’s product? So **other** modules that `import` it can
resolve `M::F::…` without re-running that package.

**Consumer contract (current lookup paths):**

| Used across finished export envs? | What |
|-----------------------------------|------|
| **Yes** | `definitions` — theorems, props, abstract props, identifiers (release / expand-by-def), axioms, structs, … |
| **No** | `facts` (known-fact indexes / `facts_by_id` search) |
| **No** | `well_defined_objects` as a cross-module known-WD library |
| **No** | `prop_rewrite_properties` / most `special_object_properties` walks (live exec-env stack only) |

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

**lkb implication:** MVP caches **definitions-only**. A later full-`ExecEnv`
blob remains optional if cold-isomorphism for facts/WD is ever required.

---

## Locked: when to read / rebuild / write (pycache rhythm)

Same **frequency model** as Python `__pycache__`: check on import (and on
`-r` while building deps); miss or stale → rebuild; success → write back.
Difference from CPython: **staleness is content-addressed**, not mtime-only.

### Write-back

| Rule | |
|------|--|
| **When** | Imported module **successfully** cold-built |
| **Create / overwrite** | Missing or rebuilt → write/replace |
| **Do not write** | Cache hit; soft Fail / FailToImport / SessionError; partial export failure; Unsupported encode (best-effort skip) |

### Dirty / must rebuild

| Rule | |
|------|--|
| **Authority** | Fingerprint (this module’s `.lit` + `litex.config`, transitive deps, `KB_ABI`) |
| **Hit** | Match → load + remap; skip re-`exec_stmt` for that module’s exports |
| **Miss** | Missing / mismatch / corrupt / ABI mismatch → cold then write-back |
| **mtime** | Never the sole validity check |

---

## Locked: load remap (session view → new Runtime)

See **Design locked §6** for the short form. Detail:

### 1. Monotonic `GlobalIds` (uniform per-counter delta)

```text
delta = runtime.now - cached_enter
every id of that kind in the env  += delta
runtime.now  = cached_leave + delta
```

Multi-export modules advance a **cursor** like cold build: each export remaps
against the current cursor, then cursor becomes that export’s remapped leave.

### 2. `global_mod_id` (path-anchored table)

| In the blob | Meaning | New value |
|-------------|---------|-----------|
| self’s old mod id | this imported module | this session’s `path_to_mod_id[self]` |
| dep’s old mod id | an import that module used | this session’s `path_to_mod_id[dep]` |

**`export_file_id` does not remap.** Layout change ⇒ fingerprint miss ⇒ rebuild.

### Implementation note

Plain `IdentifierId` and qualified `mN::fK::…` sit inside AST (and would sit in
IR keys if a full env were cached). Remap **rewrites AST** for the definitions
subset. Full-env remaps would also rebuild `HashMap` keys — same two families.

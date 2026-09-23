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

Implementation may lag this README. Wiring into `run_import_module` comes after
format / fingerprint / remap contracts are fixed.

---

## What this folder is for (Rust package)

Code under `src/new_pipeline/knowledge_base/` will eventually handle:

1. **Fingerprint** — content-addressed key over this module’s sources + configs,
   transitive deps, std roots/contents, and Litex kernel / KB ABI version.
2. **Serialize** — dump a finished import product
   (`ImportedModule`-shaped: ordered `Vec<ExportFileAndItsExecEnv>`) to disk
   (binary fast path; optional JSON as a human-readable projection).
3. **Load + remap** — if fingerprint matches, restore envs into
   `GlobalModuleManager` instead of re-running exports; remap `GlobalIds`
   ranges and session `global_mod_id` (path-anchored) so citations stay valid.
4. **Write-back** — after a successful cold (or dirty) run of an import module,
   refresh the on-disk artifact for later sessions (pycache-style).

**Non-goals (for this package):** running `.lit` itself; changing verifier
math; caching root-only export prefixes as a first product (MVP is whole
import modules).

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

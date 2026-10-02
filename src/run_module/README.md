# run_module — run packages by `litex.config`

Orchestrates **config → mount → run `.lit` → record env**.
Does not parse statements or verify facts (those stay in `parse` / `execute`).

`module_manager/` owns tables + config parse + mount APIs (no `.lit` execution).
This package **calls** those APIs and runs files.

| Related | Link |
|---------|------|
| LaunchCommand design | [`../run/README.md`](../run/README.md) |
| Module tables / `::` | [`../module_manager/README.md`](../module_manager/README.md) |
| Fixtures | [`examples/module_manager/`](../../../examples/module_manager/) |

## Layout

| File | Owns |
|------|------|
| `load_config.rs` | Find `litex.config`, read, `parse_litex_config` (incl. `std_root`); `load_config_or_empty` |
| `mount_cwd_config.rs` | `-e` / bare REPL: mount cwd config (missing → empty) |
| `run_export_file.rs` | Run one export `.lit`; set mod/export ids; record env |
| `import_kb.rs` | Import KB hit + cold write-back (always on) |
| `run_import_module.rs` | One imported package: recurse imports, then KB hit or cold exports |
| `run_project.rs` | Root / `-r`: root imports then root exports; optional `-session` |
| `run_file_with_config.rs` | `-f`: directory-local config mount + target file |

## Run order (`-r`)

```text
run_project(root):
  cfg = load_config(root, std_root)          # missing → Err
  for imp in cfg.imports:
      run_import_module(...)                 # soft fail → FailToImport
                                             # try KB hit; else cold exports + write
  for exp in cfg.exports:
      run_export_file(...)                   # soft fail → FailToImport
```

KB design contract: [`../knowledge_base/README.md`](../knowledge_base/README.md)
(definitions-only product, fingerprint, remap; always-on import cache).

## Run order (`-f`)

```text
run_file_with_config(file):
  dir = parent(file)                         # no ancestor search
  cfg = load_config_or_empty(dir)            # missing → empty / isolated
  if cfg empty: run file alone; return
  run all imports
  if file in cfg.exports:
      run exports up to and including file
  else:
      run all exports, then file as extra
  mount soft fail → FailToImport
  target soft fail → normal RunFile failure
```

## Run order (`-e` / bare REPL)

```text
mount_cwd_config():
  cfg = load_config_or_empty(cwd)            # missing → empty / no-op
  run all imports + all exports
  mount soft fail → FailToImport
then:
  -e: begin Eval env, run code
  REPL: begin Repl env, interactive loop
```

`[import std]` is path sugar only (`std_root/Name`).
`-session` keeps the last target/eval env open and enters REPL.

Import aliases are package-local. Before calling `mount_module`, the loader
chooses a free global display label (`alias`, or a free `alias__mN` on collision).
The source alias stays in its original config; canonical path → module ID
continues to determine ownership and same-path merging. This applies equally
to cold imports and cache hits, including a changed dependency traversal order.
See [the actual dependency fixture](../../examples/module_manager/cross_file_identity/README.md)
and `cross_file_identity_tests` for correct values, wrong-owner rejection,
same-path aliases, authored suffix collisions and real cache skips.

## Non-goals

- Topological sort file (config order + recursion is enough)
- Extra `ensure_imports_ready` pass after recursion

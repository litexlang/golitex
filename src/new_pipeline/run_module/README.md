# run_module — run packages by `litex.config`

Orchestrates **config → mount → run `.lit` → record env**.
Does not parse statements or verify facts (those stay in `parse` / `execute`).

`module_manager/` owns tables + config parse + mount APIs (no `.lit` execution).
This package **calls** those APIs and runs files.

## Layout

| File | Owns |
|------|------|
| `load_config.rs` | Find `litex.config`, read, `parse_litex_config` (incl. `std_root`); `load_config_or_empty` for `-f` |
| `run_export_file.rs` | Run one export `.lit`; set mod/export ids; record env |
| `run_import_module.rs` | One imported package: recurse imports (config order), then exports |
| `run_project.rs` | Root / `-r`: root imports then root exports; optional `-session` |
| `run_file_with_config.rs` | `-f`: directory-local config mount + target file |

## Run order (`-r`)

```text
run_project(root):
  cfg = load_config(root, std_root)
  for imp in cfg.imports:                    # config order
      run_import_module(imp.path, imp.alias) # missing/broken → FailToImport
  for exp in cfg.exports:
      run_export_file(exp)                   # current_mod_id = None
      # soft Failed → FailToImport (stop)

run_import_module(dir, alias):
  if already done(dir): return
  if currently running(dir): FailToImport (cycle)
  cfg = load_config(dir, std_root)
  for imp in cfg.imports:
      run_import_module(imp.path, imp.alias)
  mount(alias, dir, cfg)                     # fail → FailToImport
  for exp in cfg.exports:
      run_export_file(exp)                   # current_mod_id = Some(mod_id)
      # soft Failed → FailToImport
  mark done(dir)
```

## Run order (`-f`)

```text
run_file_with_config(file):
  dir = parent(file)                         # no ancestor search
  cfg = load_config_or_empty(dir)            # missing → empty / isolated
  if cfg empty: run file alone; return
  run all imports
  if file in cfg.exports:
      run exports up to and including file   # later exports skipped
  else:
      run all exports, then file as extra    # not an entry contract
  mount soft fail → FailToImport
  target soft fail → normal RunFile failure
```

`[import std]` is path sugar only (`std_root/Name`); same `run_import_module` path.
`-session` keeps the last target file env open and enters REPL.

## Non-goals

- Topological sort file (config order + recursion is enough)
- Extra `ensure_imports_ready` pass after recursion

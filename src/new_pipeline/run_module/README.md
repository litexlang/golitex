# run_module — run packages by `litex.config`

Orchestrates **config → mount → run `.lit` → record env**.
Does not parse statements or verify facts (those stay in `parse` / `execute`).

`module_manager/` owns tables + config parse + mount APIs (no `.lit` execution).
This package **calls** those APIs and runs files.

## Layout

| File | Owns |
|------|------|
| `load_config.rs` | Find `litex.config`, read, `parse_litex_config` (incl. `std_root`) |
| `run_export_file.rs` | Run one export `.lit`; set mod/export ids; record env |
| `run_import_module.rs` | One imported package: recurse imports (config order), then exports |
| `run_project.rs` | Root / `-r`: root imports then root exports; optional `-session` |

## Run order

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

`[import std]` is path sugar only (`std_root/Name`); same `run_import_module` path.
`-session` keeps the last root export env open and enters REPL.

## Non-goals

- Topological sort file (config order + recursion is enough)
- Extra `ensure_imports_ready` pass after recursion
- Project-aware `-f` (still bare unless added later)

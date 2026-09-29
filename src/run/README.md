# `run` — LaunchCommand design

How each CLI launch form builds a `Runtime`, mounts modules (if any), and
finishes. Companion packages:

| Package | Owns |
|---------|------|
| `launch_command.rs` | Parse argv → `LaunchCommand` |
| `run/` (this package) | Dispatch + `-e` / REPL / outcome types |
| `run_module/` | Config load + import/export mount orchestration |
| `module_manager/` | Tables, parse, mount APIs, name elaborate (no `.lit` run) |

## LaunchCommand → runner

| `LaunchCommand` | CLI | Runner | Config root |
|-----------------|-----|--------|-------------|
| `Help` / `Version` | `-help` / `-version` | print and exit | none |
| `Repl` | bare `litex` | `run_repl` | **cwd** `litex.config` (missing → empty) |
| `Eval` | `-e <code>` | `run_eval` | **cwd** `litex.config` (missing → empty) |
| `File` | `-f <file>` | `run_file` → `run_file_with_config` | **parent(file)** (missing → empty / isolated) |
| `Repository` | `-r <dir>` | `run_repo` → `run_project` | **`<dir>`** (missing → hard error) |

Shared flags (where allowed): `-session` (keep last env → REPL), `-strict`
(forbid `trust` / `trust have` / `abstract_prop`), `-lang en|zh` (JSON /
status output language; default `en`).

## Shared mount contract

When a config is non-empty:

1. Recurse `[import]` / `[import std]` in config order (`run_import_module`).
2. Run selected `[export]` `.lit` files (`run_export_file`), each in its own
   file `ExecEnv`, then record into `GlobalModuleManager`.
3. Soft Failed during mount → `RunSessionError::FailToImport` (session stop).
4. Cross-file cites use recorded envs + `::` / `:::` elaborate — not one merged
   live `ExecEnv`.

`[import std] Alias = Name` (or bare `N`) is path sugar to `<std_root>/Name`.

## Per-command flow

### `-r <repository>` (`run_project`)

```text
cfg = load_config(repo)                 # must exist, non-empty [export]
abort placeholder file env
set_root_config(cfg)
for import in cfg.imports: run_import_module(...)
for export in cfg.exports: run_export_file(...)
if -session on last export: keep env → REPL
```

Any mount soft fail → `FailToImport`. Outcome: `RunRepoResult` with `files[]`.

### `-f <file>` (`run_file_with_config`)

```text
dir = parent(file)                      # no ancestor search
cfg = load_config_or_empty(dir)
if cfg empty:
    run file alone (isolated)
else:
    run all imports
    if file in cfg.exports:
        run exports up to and including file
    else:
        run all exports, then file as an extra file
mount soft fail → FailToImport
target soft fail → normal RunFile failure (not FailToImport)
if -session: keep target env → REPL
```

### `-e <code>` (`run_eval`)

```text
abort placeholder Eval env
mount_cwd_config()                      # missing → Done / no-op
begin Eval env
run code
if -session and success: REPL
```

### Bare REPL (`run_repl`)

```text
abort placeholder Repl env
mount_cwd_config()
begin Repl env
interactive loop
```

Mount soft fail on REPL maps to a hard `RuntimeError` (no `RunRepl` payload).

### Help / Version

No Runtime, no config.

## Outcome sketch

| Outcome | Soft Failed stmts | Mount FailToImport | Hard RuntimeError |
|---------|-------------------|--------------------|-------------------|
| `RunFile` / `RunEval` / `RunRepo` | in `statement_results`, `success: false` | `session_error: FailToImport` | often `Err(...)` before/around run |
| `RunRepl` | printed per step | start fails as `Err` | `Err` |

Process exit uses `outcome.process_failed()` (false success or session error).

## Examples

Runnable fixtures: [`examples/module_manager/`](../../../examples/module_manager/).

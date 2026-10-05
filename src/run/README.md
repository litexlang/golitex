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
| `File` | `-f <file>` | `run_file_with_config` | **parent(file)** (missing → empty / isolated) |
| `Repository` | `-r <dir>` | `run_project` | **`<dir>`** (missing → hard error) |

Shared flags (where allowed): `-session` (keep last env → REPL), `-strict`
(forbid `trust` / `trust have`; allow `abstract_prop` signatures), `-lang en|zh|zh-hant|fr|ru|es|ar|ja|ko|vi` (JSON /
status output language; default `en`).

The argv item immediately after `-e` is source data. Its leading minus or exact
spelling of a shared flag does not make it a CLI option; shared flags before
or after that complete source operand retain their usual meaning.

## Source-string transaction order

`run_litex_code` tokenizes the complete source first, then parses and executes
one top-level `TokenBlock` before parsing the next. A claim/thm/sketch and its
complete nested proof form one block; parsing never executes part of a proof.

Each block uses temporary copies of the existing parse scopes. The lexical
depth is unchanged: index 0 must remain the file root for export qualification.
`exec_stmt` already discards its temporary execution environment on failure,
but that cannot undo names registered earlier by the parser. The run boundary
therefore keeps the temporary parse scopes only after successful execution;
soft failure or a parse/execution error restores the original scopes. Global
IDs keep increasing and are never restored or reused.

```text
have k N = -1  # verification fails; k is removed from parse visibility
have k N = 1   # parsed after rollback, so k can be defined successfully
k = 1
```

The overall run above still reports failure for the first statement, while
the successful correction is committed. Soft failures continue to the next
block. A parse/execution error stops the run and is reported in `session_error`,
alongside the already executed statement results. Earlier successful blocks
remain committed. For example, `let a = 1` followed by `let b =` commits a
and restores the failed b binding. A tokenizer error anywhere still prevents
all execution because tokenization happens before the block loop.

Run results retain each complete parsed statement in readable form alongside
its execution result, including soft failures. Normal, Compact and Detailed run JSON
use this source text rather than reconstructing a declaration or theorem call
from its published facts. This presentation metadata does not change parse
transactions, execution, commit or rollback.
Rust callers constructing `RunLitexCodeResult` directly include `statement_texts`;
`RunLitexCodeResult::new` defaults it to empty for source-free result trees.

The CLI emits failed Normal JSON for recognized `-e` / `-f` / `-r` commands
even when tokenization or I/O fails before a run result exists. Extraction
errors use the artifact error envelope. Invalid launch arguments still use
stderr and exit code 2. The REPL prints `success` for accepted blocks and
Normal JSON for soft failures, preserving the live session.
Hard REPL errors are reported once by the caller. In `-session`, the final
batch JSON keeps the initial source's statement results and adds the REPL error;
the pre-REPL JSON snapshot keeps citations intact after the environment aborts.
interactive parse/tokenizer diagnostics use `<repl>` rather than the initial
file or `<eval>`. The REPL text is English; `-lang` selects JSON field names
and explanations. Non-UTF-8 argv is a launch error rather than a panic.
Closing a stdout pipe discards further output while preserving the command's
exit status; other stdout I/O errors are reported as runtime errors.

An internal invariant conflict returns `RuntimeError::InternalBug`, a hard
session error. Its user-facing text is
`internal_bug: Litex internal bug: <specific conflict reason>` in CLI, REPL,
extraction errors, and all three JSON detail levels. It identifies a Litex
implementation bug rather than blaming the proof. The REPL aborts the session
on this error. This diagnostic contract does not promise recovery from a
partially committed internal merge error or change merge/rollback behavior.

Acceptance: `cargo test --release binding_lifecycle_tests -- --nocapture` and
`target/release/litex -strict -f examples/stmt_nodes/definition/parse_scope_transaction.lit`.

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
# mount failure: return normal JSON success=false / session_error; do not eval
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
| `RunFile` / `RunEval` / `RunRepo` | in `statement_results`, `success: false` | `session_error: "failed to import project"` | readable error in batch JSON |
| `RunRepl` | printed per step | start fails as `Err` | `Err` |

Process exit uses `outcome.process_failed()` (false success or session error).

## Examples

Runnable fixtures: [`examples/module_manager/`](../../../examples/module_manager/).

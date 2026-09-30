# Litex CLI

<!-- CLI spine: choose a command → run it → read Normal JSON (or REPL text) -->

This is the command-line reference for the current Litex pipeline (`src/`).
If Litex is not installed yet, start with the short [setup guide](setup.md).

Created and maintained by Jiachen Shen.

Read this page online: https://litexlang.com/doc/cli

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/cli.md

> **Litex is an experimental hobby project still in beta. Expect rough edges.**

## Before You Start

To install Litex, verify the installation, or choose a package for your
platform, use the short [setup guide](setup.md). To try Litex without a local
installation, use the [online playground](https://litexlang.com).

## First Run

Start the REPL:

```bash
litex
```

The REPL mounts `cwd/litex.config` when that file exists (otherwise an empty
project), then accepts interactive blocks. A single line without a trailing
colon runs immediately; finish an indented block with a blank line. Use
`exit`, `quit`, `:quit`, or end-of-input to exit. Each block prints
a short status line (`success` or `error`), not a full JSON document.

Run a `.lit` file:

```bash
litex -f "your_file.lit"
```

If the file's direct parent contains `litex.config`, Litex mounts that module
and runs the configured prefix through the file (see
[Project modules](#project-modules)). Otherwise it runs the file in isolation.
Both forms are batch runs: they emit one Normal `run` JSON document and exit.

Run Litex source directly:

```bash
litex -e "1 + 1 = 2"
```

Show the installed version:

```bash
litex -version
```

## Basic Shape

```text
litex [-strict] [-session] [-lang <en|zh>] <command>
```

With no command, `litex` starts the interactive REPL described above.

Shared flags are collected from argv and may appear before or after the command:

| Flag | Meaning |
|------|---------|
| `-strict` | Forbid user `trust`, `trust have`, and `abstract_prop`. |
| `-session` | After a successful `-e` / `-f` / `-r` run, keep the Runtime open and continue as REPL. |
| `-lang <tok>` | Output language for JSON / status text. `en` \| `english` (default) or `zh` \| `chinese`. Does not change Litex source. |

Examples:

```bash
litex -strict -e "1 = 1"
litex -session -f chapter.lit
litex -lang zh -f examples/tmp.lit
litex -f examples/tmp.lit
```

The parser is a small whitelist. Unsupported options and trailing tokens are
rejected. Both `-strict -e "1 = 1"` and `-e "1 = 1" -strict` work.
Keep the source string quoted as one argument.

The current whitelist does not include `-compact`, `-detailed`, `-runner`,
`-before`, `-isolated`, graph flags, or `-lean`. Those older command recipes
are not entrypoints for this build. Rust projection APIs are separate from CLI flags.

`-strict` rejects `trust`, `trust have`, and `abstract_prop` when executed.
It still accepts `axiom` and named set-theoretic releases; imported cache hits
are not rerun as a fresh strict audit. See the
[trust boundary](Manual.md#trust-and-strict-mode).

## Commands

| Command | Behavior |
|---------|----------|
| `litex` | Mount `cwd/litex.config` when present, then start the interactive REPL. |
| `litex -e <code>` | Mount `cwd/litex.config` when present, then run the source string. |
| `litex -f <file>` | Mount `parent(file)/litex.config` when present; otherwise run the file alone. |
| `litex -r <directory>` | Require `<directory>/litex.config`, mount all imports, then run all exports. |
| `litex -extractpython <code\|-f\|-r>` | Verify extractable fragments, then emit a Python `extracted_code` artifact (experimental). |
| `litex -extractc <code\|-f\|-r>` | Same as above, emitting a C99 fragment (experimental). |
| `litex -help` | Print usage text. |
| `litex -version` | Print `Litex <version>`. |

`-extractpython` / `-extractc` do not take `-session` or `-strict`. For `-f`,
source must contain `# [-extract]` / `# [end of -extract]` marker pairs; only
those blocks are verified and translated. Inline code and `-r` use whole-input
semantics. Details: [`src/extract_executable_code/README.md`](../src/extract_executable_code/README.md).

`-e` values must be the next token and must not start with `-`. Source that
begins with `-` belongs in a `.lit` file and should be run with `-f`.

Launch and mount details live in
[`src/run/README.md`](../src/run/README.md) and
[`src/module_manager/README.md`](../src/module_manager/README.md).

## Statement outcomes

Internally, each statement ends in one of three ways:

| Internal | Meaning | Parent env | Session |
|----------|---------|------------|---------|
| **Success** | Statement completed | merge temp → parent | continue |
| **Failed** | Soft miss (search / WD / similar) | discard temp | **continue** |
| **SessionError** | Hard failure | no merge | **stop** |

Batch JSON presents those outcomes as:

| Internal | In Normal JSON |
|----------|----------------|
| Success | statement `"success": true`; run `"success": true` when every stmt succeeded and there is no session error |
| Failed | statement `"success": false` **inside** `statement_results` (presentation may say “error”; Rust stays Failed) |
| SessionError | top-level `"session_error"` set; session must stop |

Soft Failed statements stay in `statement_results`. They are **not** lifted into
a top-level `verify_error` that clears the array. Process exit is nonzero when
any Failed occurred or a SessionError occurred.

A soft miss is not a proof that the proposition is false. It means the current
routes did not establish it (or well-definedness failed). Add a smaller fact,
fix a domain obligation, or repair the statement.

## JSON Output Contract

`-e`, `-f`, and `-r` batch outcomes emit one Normal `run` document on stdout.
Launch, tokenization/parsing, or early I/O errors can instead produce text on
stderr with no JSON document. A successful `-session` enters the text REPL
before the batch JSON is printed, so its stdout is not one standalone JSON value.
The projection
is defined in [`src/json_output/README.md`](../src/json_output/README.md).
It does **not** dump the full verify/exec IR; that tree remains available for
the Rust Detailed projection and other tooling.

### Run envelope

```json
{
  "kind": "run",
  "success": true,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "language": "en",
  "statement_results": [],
  "session_error": null
}
```

| Field | Meaning |
|-------|---------|
| `kind` | Always `"run"` for verifier batch commands |
| `success` | `true` iff every statement succeeded and `session_error` is null |
| `target` | `"eval"`, `"file"`, or `"repo"` |
| `path` | `null` for `-e`; requested path for `-f` / `-r` |
| `detail` | `"normal"` for the default CLI projection |
| `language` | `"en"` or `"zh"` from `-lang` (default `"en"`); Chinese output localizes the keys too |
| `statement_results` | `-e` / target `-f` statements in order; the current `-r` summary leaves this array empty |
| `session_error` | Hard stop payload, or `null` |

Programs should read `success`, `statement_results`, and `session_error`. Exit
status `0` means batch success; `1` means a failed run or a parse/I/O error;
`2` means an invalid-argument error returned to the launcher. An invalid
statement captured as a session error is a failed run and exits `1`.
For machine consumers, use `-lang en`, require exit `0`, parse the JSON, and
require `kind == "run"`, `success == true`, and `session_error == null`.
The current envelope has no `ok` field. `-r` computes overall success from
its files but does not serialize their statement arrays into this summary.
Use `-f` on a target file when you need its statement explanations.

### Chinese output

`litex -lang zh -e "1 = 1"` localizes the envelope and statement keys as well
as proof explanations. Enum-like envelope values such as `run`, `eval`, and
`normal` remain English:

```json
{
  "种类": "run",
  "成功": true,
  "目标": "eval",
  "路径": null,
  "详细度": "normal",
  "语言": "zh",
  "语句结果": [
    {
      "成功": true,
      "语句": "1 = 1",
      "证明方法": {
        "类型": "内置规则",
        "规则名": "由内部表示相等",
        "说明": "两边具有相同的内部表示"
      },
      "存储": [
        "1 = 1"
      ],
      "推断": []
    }
  ],
  "会话错误": null
}
```

### Normal statement shape

Success:

```json
{
  "success": true,
  "statement": "0 <= k",
  "proof_method": {
    "type": "known_atomic_fact",
    "cite": "0 <= k"
  },
  "stores": ["0 <= k"],
  "infers": []
}
```

Soft failure (still inside `statement_results`):

```json
{
  "success": false,
  "statement": "a > 10",
  "why_failed": {
    "phase": "search_proof",
    "goal": "a > 10"
  },
  "stores": [],
  "infers": []
}
```

Rules:

- `success` is a bool (not an `outcome` string).
- `stores`, `infers`, `cite`, `statement`, and `goal` use readable Litex text.
- Builtin explanations use `rule_name` and `message`, not the old `rule` tag.
- Normal skips well-definedness subtrees; look at `why_failed.phase` when a
  statement did not succeed.

### Examples

Successful inline run:

```json
{
  "detail": "normal",
  "kind": "run",
  "language": "en",
  "success": true,
  "path": null,
  "session_error": null,
  "statement_results": [
    {
      "infers": [],
      "statement": "1 = 1",
      "stores": ["1 = 1"],
      "success": true,
      "proof_method": {
        "type": "builtin_rule",
        "rule_name": "Equal by IR",
        "message": "Both sides share the same internal representation"
      }
    }
  ],
  "target": "eval"
}
```

Soft miss with a successful prefix retained:

```json
{
  "detail": "normal",
  "kind": "run",
  "language": "en",
  "success": false,
  "path": null,
  "session_error": null,
  "statement_results": [
    {
      "infers": [],
      "statement": "have a R",
      "stores": ["a $in R"],
      "success": true,
      "proof_method": { "type": "define_obj" }
    },
    {
      "infers": [],
      "statement": "a > 10",
      "stores": [],
      "success": false,
      "why_failed": {
        "goal": "a > 10",
        "phase": "search_proof"
      }
    }
  ],
  "target": "eval"
}
```

### Help and version

`litex -help` prints plain usage text. `litex -version` prints
`Litex <version>`. Invalid argument combinations print a short `launch_error: ...`
line on stderr and exit with code `2`.

## Session Flag

`-session` is not a separate framed protocol. It means: after a **successful**
`-e`, `-f`, or `-r` run, keep the last Runtime environment and continue in the
ordinary REPL. Failed batch runs do not enter that REPL.

Example:

```bash
litex -session -f chapter.lit
```

## Project Modules

There is no `submodule` and no `[hierarchy]`. `[export]` lists `.lit` files
only. `[import]` / `[import std]` mount modules under one shared alias
namespace (`[import std]` bare `N` means `N = N`; `Alias = StdName` resolves
to `<std_root>/<StdName>`).

Fixtures:
[`examples/module_manager/`](../examples/module_manager/).

Use `litex.config` to organize a module:

- select each participating `.lit` file exactly once, in mathematical order,
  under `[export]` (files only; no child-folder export);
- declare external module folders under `[import] Alias = path` and std
  packages under `[import std]` as either bare `N` or `Alias = StdName`;
- keep import aliases unique across both import sections;
- cite mounted packages and exports with canonical names, such as
  `Algebra::chap1::name` or `basics:::name`.

`[export]` is an explicit selection list, not a directory inventory. Unlisted
files are sidecars: discovery does not parse or execute them. Source-level
`import` is rejected in files and in the REPL; project source uses its manifest.
Imported modules may load a matching `__litex_knowledge_base__/` cache; on a
miss, Litex executes their exports and attempts a cache write-back. This applies
to strict runs too. Root exports follow the execution order below.

### Mount behavior

| Command | Config lookup | Mount behavior |
|---------|---------------|----------------|
| `litex -r <dir>` | `<dir>/litex.config` (required) | all imports, then all exports |
| `litex -f <file>` | `parent(file)/litex.config` (missing → empty) | if listed: imports + exports through that file; if unlisted: all exports then the file; if no config: isolated |
| `litex -e <code>` | `cwd/litex.config` (missing → empty) | all imports + all exports, then eval |
| bare `litex` | `cwd/litex.config` (missing → empty) | all imports + all exports, then REPL |

Mount soft Failed → session `FailToImport`. For `-f`, soft Failed on the
**target** file itself is a normal file failure, not `FailToImport`.

## Lean compiler boundary

The current Cargo build registers only the `litex` binary and does not include
the earlier `stmt_result_to_lean_compiler` Rust module. There is no working
Lean compilation command in this CLI. The wrapper and generated examples in
[`lean/`](../lean/) are retained experimental artifacts; the wrapper refers
to a binary target that is absent from the current build. They are not
acceptance evidence for a current `src/` verification run.

## Practical Recipes

```bash
litex -e "1 = 1"
litex -f examples/tmp.lit
litex -r examples/module_manager/repo
litex -strict -f examples/tmp.lit
litex -session -f examples/tmp.lit
```

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
`exit`, `quit`, `:quit`, or end-of-input to exit. Successful blocks print
`success`. A failed verification prints Normal JSON with the original
statement and failure reason, then accepts the next block. Hard session
errors stop the REPL and are reported once. In a continued `-session`, the
final JSON retains the initial batch's statement results and adds the hard
error. Interactive parse/tokenizer errors refer to `<repl>`.

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
litex [-strict] [-session] [-lang <en|zh|zh-hant|fr|ru|es|ar|ja|ko|vi>] <command>
```

With no command, `litex` starts the interactive REPL described above.

Shared flags outside command operands may appear before or after the command:

| Flag | Meaning |
|------|---------|
| `-strict` | Forbid user `trust`, `trust have`, and `axiom`; allow abstract predicate declarations and named foundation releases. |
| `-session` | After a successful `-e` / `-f` / `-r` run, keep the Runtime open and continue as REPL. |
| `-graph` | With `-e` / `-f` / `-r`, emit mathematical dependency JSON instead of Normal output; excludes `-session`. |
| `-lang <tok>` | Output language for JSON verification feedback: `en` (default), `zh`, `zh-hant`, `fr`, `ru`, `es`, `ar`, `ja`, `ko`, or `vi`. Does not change Litex source or verification. |

Examples:

```bash
litex -strict -e "1 = 1"
litex -strict -e '-2 < 0'
litex -session -f chapter.lit
litex -lang zh -f examples/tmp.lit
litex -lang fr -e '1 + 1 = 2'
litex -f examples/tmp.lit
```

The parser is a small whitelist. Unsupported options and trailing tokens are
rejected. Both `-strict -e "1 = 1"` and `-e "1 = 1" -strict` work.
Keep the source string quoted as one argument. The shell removes the quotes;
the argv item immediately following `-e`, or an inline extraction command,
is consumed as source, including a leading minus or an exact option spelling.
The next item after `-f` / `-r` is likewise a path even if it starts with `-`.
For extraction, `-f` / `-r` immediately after the command select file/repository
input; their next item is the path. For example, `-e '-strict'`
passes `-strict` to the Litex parser and fails as invalid source; it does not
enable strict mode or start a REPL.

The current whitelist does not include `-compact`, `-detailed`, `-runner`,
`-before`, `-isolated`, `-factgraph`, or `-defgraph`. Those older command recipes
are not entrypoints for this build. Rust projection APIs are separate from CLI flags.

`-strict` rejects user `trust`, `trust have`, and `axiom` when executed,
including nested proof statements and imported dependencies. An `abstract_prop`
declaration is allowed: it introduces only a predicate signature, with no
proved instances. Calls still require valid arguments, exact arity and proof.
Named set-theoretic releases remain allowed. Strict imports bypass cached
environments and re-execute dependency sources with the same policy. See the
[trust boundary](Manual.md#trust-and-strict-mode).

## Commands

| Command | Behavior |
|---------|----------|
| `litex` | Mount `cwd/litex.config` when present, then start the interactive REPL. |
| `litex -e <code>` | Mount `cwd/litex.config` when present, then run the source string. |
| `litex -f <file>` | Mount `parent(file)/litex.config` when present; otherwise run the file alone. |
| `litex -r <directory>` | Require `<directory>/litex.config`, mount all imports, then run all exports. |
| `litex -lean -f <file>` | Verify a standalone file and replay supported typed results into Lean source on stdout (preview). |
| `litex -extractpython <code\|-f\|-r>` | Verify extractable fragments, then emit a Python `extracted_code` artifact (experimental). |
| `litex -extractc <code\|-f\|-r>` | Same as above, emitting a C99 fragment (experimental). |
| `litex -help` | Print usage text. |
| `litex -version` | Print `Litex <version>`. |

`-extractpython` / `-extractc` do not take `-session` or `-strict`. For `-f`,
source must contain `# [-extract]` / `# [end of -extract]` marker pairs; only
those blocks are verified and translated. Inline code and `-r` use whole-input
semantics. Details: [`src/extract_executable_code/README.md`](../src/extract_executable_code/README.md).

Source and path operands must be the next argv item and must be nonempty.
Both `litex -e '-2 < 0'` and `litex -extractpython '-2 < 0'` are valid.
All argv items must be valid UTF-8; invalid bytes produce a launch error with
exit code `2`. `-lang` selects JSON keys and explanations; usage text, REPL
prompts and `success` feedback remain English.

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
Tokenization, parsing and early I/O failures also produce a failed Normal
document with `session_error`. Invalid command-line shapes still produce text
on stderr with exit code `2`, because no command was selected. Extraction
failures produce a failed artifact document with `error`. Success and failure
artifacts share `format`, `target`, `path`, `output_path`, and `language`, and
their field names follow `-lang`. A successful `-session` enters the text REPL
before the batch JSON is printed, so its stdout is not one standalone JSON value.
The projection
is defined in [`src/json_output/README.md`](../src/json_output/README.md).
It does **not** dump the full verify/exec IR; that tree remains available for
the Rust Detailed projection and other tooling.
When a downstream reader closes stdout, Litex preserves the command's exit
status without panicking. Other output I/O errors are reported normally.

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
| `language` | Selected locale from `-lang`: `"en"`, `"zh"`, `"zh-hant"`, `"fr"`, `"ru"`, `"es"`, `"ar"`, `"ja"`, `"ko"`, or `"vi"` (default `"en"`); non-English output localizes known keys too |
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

`statement` preserves the complete parsed source in readable form, including
theorem/axiom names, theorem arguments and selected conclusions. Computed or
published facts belong in `stores`. For `1 / 0 = 0`, the failed statement stays
`1 / 0 = 0`; `why_failed.phase` is `well_defined` and its message says that
well-definedness could not be proved. This is a proof failure, not an assertion
that every unproved expression is mathematically undefined.

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
Ordinary runs may load a matching `__litex_knowledge_base__/` cache; on a
miss, Litex executes the imported exports and attempts a cache write-back.
Strict runs always execute imported source exports instead of replaying the
cache. Root exports follow the execution order below.

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

`litex -lean -f <file>` is a preview output mode of the ordinary `litex` binary.
It verifies a complete standalone file once, then consumes typed winning
results, object WD and scoped citations. Success writes only Lean source to
stdout. Verification or unsupported-compilation failures return nonzero,
write diagnostics to stderr and emit no partial Lean artifact.

```sh
litex -strict -lean -f lean/examples/real_is_complex/statement.lit
```

The initial slice covers reflexivity, sethood, exact integer R/C membership,
ordinary forall introduction, R-to-C membership and certified add/div objects.
Support depends on the actual proof route. Rational normalization and other
unsupported routes fail even if another Core theorem could prove the conclusion.
Sessions, repository mode, other output modes and module configurations/imports
are not supported by this first slice.

The final artifacts are [lean/Litex.lean](../lean/Litex.lean) and
[lean/examples/](../lean/examples/), with a problem folder per source/generated
pair. Development tools and plans are local-only in `scripts/litex_to_lean/`;
older material remains in `scripts/legacy_to_lean/`. Emission is distinct from
Lean kernel checking, and the numeric model does not yet interpret all Litex.

## Practical Recipes

```bash
litex -e "1 = 1"
litex -f examples/tmp.lit
litex -r examples/module_manager/repo
litex -strict -f examples/tmp.lit
litex -session -f examples/tmp.lit
```

## Mathematical dependency graphs (preview)

Use `-graph` with `-e`, `-f` or `-r` to emit one mathematical dependency JSON
document. Nodes are definitions, reusable theorems and accepted facts. Calls
such as `by thm` contribute relationships and source details, not nodes.

```bash
litex -graph -strict -f examples/stmt_nodes/graph/math_dependencies.lit > graph.json
python3 src/graph/render_html.py graph.json graph.html
```

Open `graph.html` in a browser, or open
[`math_graph_viewer.html`](assets/math_graph_viewer.html) and select the JSON.
Inferred/local facts are folded by default and can be expanded. Selecting a
node shows its mathematical statement and related facts; selecting an edge
shows its source and premise group. Time order is not a dependency.

`-strict` retains its ordinary verification meaning. Schema keys, relationship
types and IDs are independent of `-lang`; IDs belong to this run. The viewer
has English/Chinese interface copy and uses source mathematics as labels.
Other selected output locales preserve the same data with the English viewer
interface. Successful graphs have `success: true` and exit 0. Verification or
input failures exit 1, retain available history and diagnostics, and never
publish failed facts. Invalid launch combinations exit 2. `-graph` excludes
REPL/`-session`, LaTeX conversion and executable extraction.

Local assumptions remain scoped; trust and external records retain their
origin. A cached interface can be available without the original proof
history. Graph output is a dependency view, not an independent proof replay.
See the [schema and ownership guide](../src/graph/README.md).

## LaTeX conversion (preview)

`litex -latex -lang zh -e '1 = 1'` compiles parsed source into a LaTeX
artifact. `-f <file>` selects a standalone file or the registered project prefix
through that file; `-r <project>` converts root exports in manifest order.
Dependency manifests supply names; dependency source is not executed or emitted.

Use `-latex -document` for a complete XeLaTeX article, or omit `-document` for
a fragment. All ten `-lang` choices select complete mathematical prose templates.
The JSON keys stay stable across locales; `content` contains LaTeX, `success`
reports conversion, and `verified` is always false. On conversion failure `content` is null
and the process exits 1. Invalid launch arguments produce stderr and exit 2,
through the common argument parser. Conversion does not execute or verify source; `-strict`
and `-session` are rejected. See the [compiler guide](../src/compile_to_latex/README.md)
for saving `.tex`, the font/package requirements, API and coverage.

Internally `CompileToLatex` and `ExtractExecutableCode` are separate launch
commands and outcome types. `-latex` goes through the normal command dispatcher;
it does not share C/Python's verification and executable extraction pipeline.

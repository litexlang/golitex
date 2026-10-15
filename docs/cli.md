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
platform, use the short [setup guide](setup.md).

Check `litex -version` and `litex -help`: this reference describes the current
checkout; an older installed release can have different flags and output.
If a project uses `[import std]`, follow the setup guide’s std-path and
compatibility-module loading checks. Ordinary native vocabulary does not
require std; the currently shipped `basics` module exports no declarations.

To try Litex without a local
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
errors stop the REPL and are reported once. In a continued `-session`, any
rejected interactive block makes the final `run_result` a failure without
marking the session terminated; a hard error additionally sets structured
termination information. Interactive parse/tokenizer errors refer to `<repl>`.

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
| `-lang <tok>` | Output language for JSON verification feedback: `en` (default), `zh`, `zh-hant`, `fr`, `ru`, `es`, `ar`, `ja`, `ko`, or `vi`. Does not change Litex source or verification. |

Examples:

```bash
litex -strict -e "1 = 1"
litex -strict -e '-2 < 0'
litex -session -f chapter.lit
litex -lang zh -f examples/claim_obtain_scope.lit
litex -lang fr -e '1 + 1 = 2'
litex -f examples/claim_obtain_scope.lit
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
| `litex -latex <-e\|-f\|-r> <input>` | Convert parsed source to a LaTeX artifact without verification (preview); see [LaTeX conversion](#latex-conversion-preview). |
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
| Success | statement `"statement_result": "accepted"`; run `"run_result": "success"` when every submitted statement was accepted and the session did not terminate |
| Failed | statement `"statement_result": "rejected"` **inside** `statement_results` (Rust stays Failed) |
| SessionError | top-level `"session_terminated": true` with structured `termination`; session must stop |

Soft Failed statements stay in `statement_results`. They are **not** lifted into
a top-level `verify_error` that clears the array. Process exit is nonzero when
any Failed occurred or a SessionError occurred.

A soft miss is not a proof that the proposition is false. It means the current
routes did not establish it (or well-definedness failed). Add a smaller fact,
fix a domain obligation, or repair the statement.

## JSON Output Contract

`-e`, `-f`, and `-r` batch outcomes emit one Normal `run` document on stdout.
Tokenization, parsing and early I/O failures also produce a failed Normal
document with `session_terminated: true` and structured `termination`. Invalid command-line shapes still produce text
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
  "run_result": "success",
  "target": "eval",
  "path": null,
  "detail": "normal",
  "language": "en",
  "statement_results": [],
  "session_terminated": false,
  "termination": null
}
```

| Field | Meaning |
|-------|---------|
| `kind` | Always `"run"` for verifier batch commands |
| `run_result` | `"success"` iff every submitted statement was accepted and the session did not terminate; otherwise `"failure"` |
| `target` | `"eval"`, `"file"`, or `"repo"` |
| `path` | `null` for `-e`; requested path for `-f` / `-r` |
| `detail` | `"normal"` for the default CLI projection |
| `language` | Selected locale from `-lang`: `"en"`, `"zh"`, `"zh-hant"`, `"fr"`, `"ru"`, `"es"`, `"ar"`, `"ja"`, `"ko"`, or `"vi"` (default `"en"`); non-English output localizes known keys too |
| `statement_results` | `-e` / target `-f` statements in order; the current `-r` summary leaves this array empty |
| `session_terminated` | Boolean hard-stop indicator; ordinary proof rejection leaves it false |
| `termination` | `null`, or `{ "phase": ..., "message": ... }` for a hard stop |

Programs should read `run_result`, `statement_results`, `session_terminated`,
and `termination`. Exit
status `0` means batch success; `1` means a failed run or a parse/I/O error;
`2` means an invalid-argument error returned to the launcher. An invalid
statement that causes a hard termination is a failed run and exits `1`.
For machine consumers, use `-lang en`, require exit `0`, parse the JSON, and
require `kind == "run"`, `run_result == "success"`,
`session_terminated == false`, and `termination == null`.
The current envelope has neither `success` nor `ok`. `-r` computes its overall
verdict from its files but does not serialize their statement arrays into this summary.
Use `-f` on a target file when you need its statement explanations.

`statement` preserves the complete parsed source in readable form, including
theorem/axiom names, theorem arguments and selected conclusions. Computed or
published facts belong in `stores`. For `1 / 0 = 0`, the failed statement stays
`1 / 0 = 0`; `why_failed.phase` is `well_defined` and its message says that
well-definedness could not be proved. This is a proof failure, not an assertion
that every unproved expression is mathematically undefined.

### Custom indexes and visualizations

Save the ordinary file output for a downstream tool:

```bash
litex -lang en -f example.lit > result.json
```

Use successful entries in `statement_results` to read declarations and theorem
calls from `statement`, and accepted mathematical facts from `stores` and
`infers`. `proof_method` provides a summary and includes readable citations for
some verification routes. These fields can support custom indexes and
visualizations without a separate graph output format.

Normal JSON does not contain every verification child or FactId citation, so
it cannot guarantee reconstruction of the complete dependency graph. The Rust
Detailed projection exposes more typed proof evidence; it is an API, not a CLI
flag. The `-r` Normal summary has an empty `statement_results` array; use `-f`
for the statement output of each target file. A failed file's successful
statement entries do not mean the file was published as a completed export.

### Chinese output

`litex -lang zh -e "1 = 1"` localizes the envelope and statement keys as well
as proof explanations. Enum-like envelope values such as `run`, `eval`, and
`normal` remain English:

```json
{
  "种类": "run",
  "运行结果": "success",
  "目标": "eval",
  "路径": null,
  "详细度": "normal",
  "语言": "zh",
  "语句结果": [
    {
      "语句判定": "accepted",
      "语句": "1 = 1",
      "证明方法": {
        "类型": "同一对象",
        "规则名": "同一对象",
        "说明": "两边内部表示相同，或绑定参数改名后结构相同"
      },
      "存储": [
        "1 = 1"
      ],
      "推断": []
    }
  ],
  "会话已终止": false,
  "终止信息": null
}
```

### Normal statement shape

Success, for `0 <= k` after `have k N` has already inferred it:

```json
{
  "statement_result": "accepted",
  "statement": "0 <= k",
  "proof_method": {
    "type": "cite_known",
    "cite": "0 <= k"
  },
  "stores": ["0 <= k"],
  "infers": []
}
```

Soft failure (still inside `statement_results`):

```json
{
  "statement_result": "rejected",
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

- `statement_result` is the explicit string `"accepted"` or `"rejected"`.
- `stores`, `infers`, `cite`, `statement`, and `goal` use readable Litex text.
- Builtin explanations use `rule_name` and `message`, not the old `rule` tag.
- Successful Normal entries summarize their proof route. Failed entries may
  include nested well-definedness or proof-block evidence under `why_failed`;
  start with `why_failed.phase` and follow its nested failure to the stopping point.

`proof_method.type` identifies the selected verification route for that
statement. Read `statement_result` and `run_result` to determine acceptance;
different successful inputs need not use the same proof-method type.

### Examples

Successful inline run:

```json
{
  "detail": "normal",
  "kind": "run",
  "language": "en",
  "run_result": "success",
  "path": null,
  "session_terminated": false,
  "termination": null,
  "statement_results": [
    {
      "infers": [],
      "statement": "1 = 1",
      "stores": ["1 = 1"],
      "statement_result": "accepted",
      "proof_method": {
        "type": "they_are_the_same",
        "rule_name": "Same object",
        "message": "Both sides have identical IR or alpha-equivalent binder structure"
      }
    }
  ],
  "target": "eval"
}
```

Selected-field excerpt of a soft miss with a successful prefix retained:

```json
{
  "detail": "normal",
  "kind": "run",
  "language": "en",
  "run_result": "failure",
  "path": null,
  "session_terminated": false,
  "termination": null,
  "statement_results": [
    {
      "infers": [],
      "statement": "have a R",
      "stores": ["a $in R"],
      "statement_result": "accepted",
      "proof_method": { "type": "define_obj" }
    },
    {
      "infers": [],
      "statement": "a > 10",
      "stores": [],
      "statement_result": "rejected",
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

**Use `-session` for iterative Litex authoring. Load the accepted prefix once,
then submit one top-level statement at a time in that same process. An ordinary
rejection keeps earlier accepted definitions and facts; repair the rejected
statement there. Do not rerun the whole file whenever you add a few lines.**

For an existing passing file:

```bash
litex -session -f chapter.lit
```

For a short comparison, start `litex -lang en -session -e 'have a R = 2'`,
then enter each statement separately. The failure JSON is abbreviated:

```text
litex> a = 3
{"run_result": "failure", ..., "session_terminated": false, "termination": null}
litex> a + 1 = 3
success
```

`a = 2` survives the ordinary rejection. Two separate `-e` commands cannot
share that context: `litex -e 'have a R = 2'` succeeds, but a later
`litex -e 'a + 1 = 3'` fails because its new process has no declaration of `a`.
Use clean batch file runs for baselines, coherent checkpoints, and final
acceptance. Hard errors can stop the REPL; restart and replay accepted source
when needed. For the agent-oriented loop and a fuller side-by-side comparison,
see [How to connect Litex to your AI agent](#how-to-connect-litex-to-your-ai-agent)
and the [Agent Guide](AgentGuide.md).

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

The current numeric slice covers reflexivity, sethood, literal N/Z/R/C membership,
ordinary forall introduction, numeric hierarchy bridges, and certified
add/sub/mul/neg/div objects with closed integer powers. Selected Rational
normalization uses explicit denotation transport and a fixed Lean normalizer;
its guarded route consumes the recorded nonzero proofs. Arithmetic constructor
congruence, exact closed calculation children and scalar division relations
also replay their own selected evidence. Support still depends on the actual
proof route and object domain; unsupported routes fail even if another Core
theorem could prove the conclusion.
Sessions, repository mode, other output modes and module configurations/imports
are not supported by this first slice.

The final artifacts are [lean/Litex.lean](../lean/Litex.lean) and
[lean/examples/](../lean/examples/), with a problem folder per source/generated
pair. Development tools and plans are local-only in `scripts/litex_to_lean/`;
older material remains in `scripts/legacy_to_lean/`. Emission is distinct from
Lean kernel checking, and the numeric model does not yet interpret all Litex.
The empty `Rational {}` result tag records a successful normalization family,
not a monomial derivation: the generated normalization proof must pass Lean.
The declaration slice adds let and typed RHS-have aliases, named theorems and
explicit theorem selections. Equality-class paths, supported argument transport
and whole-forall reuse retain exact recorded citations. Bounded atomic rewrites
support whole-argument aliases and certified closed representatives. Selected
closed-numeric equality subtree substitution retains its exact citations and
residual proof. The numeric profile includes Q hierarchy/closure, real comparison
and bounded weak-order rules, and ordinary top-level numeric have as generic
parameter contexts with actual nonempty checks. Local arbitrary-have proof steps,
function/set constructors, general inequality solving, refined carriers and
uncompiled forward-inference families remain outside the current profile.

## Practical Recipes

Run the `examples/` and `lean/examples/` commands from the repository root;
those paths belong to the checkout, not the installed package. Replace
`your_file.lit`, `example.lit`, and `chapter.lit` with files you create.

```bash
litex -e "1 = 1"
litex -f examples/claim_obtain_scope.lit
litex -r examples/module_manager/repo
litex -strict -f examples/claim_obtain_scope.lit
litex -session -f examples/claim_obtain_scope.lit
```

## LaTeX conversion (preview)

`litex -latex -lang zh -e '1 = 1'` compiles parsed source into a LaTeX
artifact. `-f <file>` selects a standalone file or the registered project prefix
through that file; `-r <project>` converts root exports in manifest order.
Dependency manifests supply names; dependency source is not executed or emitted.

Use `-latex -document` for a complete XeLaTeX article, or omit `-document` for
a fragment. All ten `-lang` choices select complete mathematical prose templates.
The JSON keys stay stable across locales; `content` contains LaTeX,
`artifact_result` is `"success"` or `"failure"`, and `verified` is always
false. On conversion failure `content` is null
and the process exits 1. Invalid launch arguments produce stderr and exit 2,
through the common argument parser. Conversion does not execute or verify source; `-strict`
and `-session` are rejected. See the [compiler guide](../src/compile_to_latex/README.md)
for saving `.tex`, the font/package requirements, API and coverage.

Internally `CompileToLatex` and `ExtractExecutableCode` are separate launch
commands and outcome types. `-latex` goes through the normal command dispatcher;
it does not share C/Python's verification and executable extraction pipeline.

A continued registered-file session keeps definition lookup attached to the
publication owner recorded by its open file environment. New diagnostics still
use `<repl>`. This includes predicates projected by refined template carriers;
lookup never borrows the live environment for a different root or imported
export ID. The [continued-export example](../examples/wd/continued_export_repl/README.md)
records the file-to-REPL workflow.

## How to connect Litex to your AI agent

Litex is built for a propose → check → revise → continue loop. An agent (or any
tool that shells out to `litex`) should treat the CLI as a live math context,
not as a one-shot script runner for every candidate line.

**Open one authoring Session and keep that process running while you repair
steps.** Load accepted definitions and facts once with `-session`, then submit
new top-level statements to the same process. An ordinary rejected statement is
discarded; earlier accepted context remains available. The agent can use the
JSON feedback to repair its next proposal without rebuilding the checked
prefix.

### One persistent Session

```bash
litex -strict -lang en -session \
  -e 'have a R = 2'
```

Then, in that same process:

```text
litex> a = 3
{"run_result": "failure", "session_terminated": false}
litex> a + 1 = 3
success
```

Record `a = 2` once. Rejecting `a = 3` leaves that fact available for checking
`a + 1 = 3`. Read `run_result`, `session_terminated`, and `termination` from the
rejection JSON (the excerpt above shows selected fields only). While
`session_terminated` is false and another `litex>` prompt appears, repair in
place.

### A fresh process for every attempt

```bash
litex -strict -lang en -e '
have a R = 2
a = 3'

litex -strict -lang en -e '
have a R = 2
a + 1 = 3'
```

The second command must replay `a = 2` before it can check `a + 1 = 3`. A long
prefix would need to be replayed too. Prefer one live Session for the inner
loop; reserve clean `-e` / `-f` runs for baselines, coherent checkpoints, and
final verification.

### Practical agent checklist

1. Start `litex -strict -lang en -session` (optionally with `-e` / `-f` to load
   an accepted prefix). Keep that process open across ordinary soft failures.
2. Submit one top-level statement at a time; finish an indented block with a
   blank line. Consume the response before sending the next candidate.
3. On plain-text `success`, journal the accepted source outside the process.
   On soft rejection (`statement_result: "rejected"`, `session_terminated: false`),
   keep the Session and repair only the failed statement.
4. At checkpoints, run a separate clean `litex -f` / `-e` gate on the saved
   file while the authoring Session can stay open. If the process stops or its
   loaded module context must change, restart and replay the journaled source.

The [website playground](https://litexlang.com) runs complete source files
separately; it is not a substitute for a persistent local Session. Full agent
workflow, restart boundaries, and quadratic-cost notes live in the
[Agent Guide](AgentGuide.md). Flag shapes and JSON fields on this page remain
the contract the agent should parse.

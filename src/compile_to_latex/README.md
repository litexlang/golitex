# Parse-only LaTeX compilation (preview)

Compile current parsed Litex syntax into mathematical LaTeX with localized prose.
The compiler reads `Stmt`, `Fact`, and `Obj`; it does not execute statements,
check truth or well-definedness, evaluate commands, or invent proof steps.

```sh
litex -latex -lang zh -e '1 = 1'
litex -latex -lang fr -f examples/stmt_nodes/compile_to_latex/identity.lit
litex -latex -lang ja -r project
litex -latex -document -lang zh -f examples/stmt_nodes/compile_to_latex/identity.lit
```

The CLI emits one JSON artifact. Its stable keys include `artifact_result`,
`format`, `target`, `path`, `language`, `verified`, `content`, and `error`.
`artifact_result` is `"success"` or `"failure"`; `verified` is always false. On failure, `content` is null,
`error` describes the source/config/conversion error, and the process exits 1.
`-session` and `-strict` do not apply to this conversion route.
Invalid launch arguments use the common CLI diagnostic path: stderr and exit 2.

Save a complete document without copying JSON escapes:

```sh
litex -latex -document -lang zh -f example.lit | python3 -c 'import json,sys; a=json.load(sys.stdin); sys.exit(a["error"]) if a["artifact_result"] != "success" else sys.stdout.write(a["content"])' > example.tex
xelatex -halt-on-error example.tex
```

## Languages and typography

Every current `OutputLanguage` variant is supported: English (`en`), Simplified
Chinese (`zh`), Traditional Chinese (`zh-hant`), French (`fr`), Russian (`ru`),
Spanish (`es`), Arabic (`ar`), Japanese (`ja`), Korean (`ko`), and Vietnamese
(`vi`). Mathematical symbols and user names are preserved across languages.
`language.rs` supplies complete prose sentences and labels, with an exhaustive
language dispatch and equal-sized phrase tables. There is no fallback language.

Default output is an embeddable fragment combining text paragraphs, inline or
display math, piecewise function arrays, and structured proof branches. Inline math uses `$...$`
(not `\(...\)`), so preview or copy paths that drop a backslash do not turn the
delimiters into literal parentheses around the formula. `-document` (or the Rust
`to_latex_document` API) adds a XeLaTeX article wrapper using `amsmath`,
`amssymb`, `fontspec`, and `geometry`. Its bundled TeX Live font recipes use:

| Locale | Additional packages/fonts |
| --- | --- |
| Latin-script locales and Russian | CMU Serif (`cmunrm.otf`, bold `cmunbx.otf`, italic `cmunit.otf`) |
| Simplified Chinese | `ctex` with the Fandol font set |
| Traditional Chinese | `ctex`, AR PL Mingti2L Big5 (`bsmi00lp.ttf`, synthetic bold) |
| Japanese | `xeCJK`, IPAex Mincho (`ipaexm.ttf`) |
| Korean | `xeCJK`, UnBatang (`UnBatang.ttf`) |
| Arabic | `polyglossia`, Amiri (`Amiri-Regular.ttf`), right-to-left prose |

A minimal TeX installation may lack these packages or fonts. Fragment users can
supply their own document typography. PDF compilation is outside the Litex CLI:
the CLI writes LaTeX, and does not install fonts or invoke a TeX engine.

## Mathematical reading layout

Theorem, definition, claim, axiom and trust labels remain explicit. A theorem or
claim with a source proof has one proof caption and an end marker; a bodyless
theorem receives neither. Proof methods introduce their bodies directly, so
nesting a case split or contradiction does not add another generic proof caption.
Sketches retain their distinct label and no completion marker. Top-level
template declarations retain their scoped quotations.

Proof bodies are continuous paragraphs. Cases and induction phases use bold
run-in labels; a contradiction's goal, contrary assumption, steps and closing
conclusion remain in that same paragraph. Nested definitions, local claims,
witnesses and explicit theorem applications inherit the inline flow. The end
marker follows the final sentence. Line wrapping is left to the typesetter or
the reader's viewport; there is no forced one-line horizontal strip.

For example, a case reads “假设 $n = 1$，则 $n = 1 \lor n > 1$。” / “Suppose
$n = 1$. Then $n = 1 \lor n > 1$.” Later steps retain localized transitions,
and the split closes by restating its common conclusion. These transitions
come from the source structure, without adding inferred reasons or proof steps.

The private `layout::Flow` owns block versus inline typography. Top-level
declarations and assertions retain their headings, field lists and display
math. Within a proof, formulas use inline mathematics with all comparisons,
quantifiers, domains and clauses intact. Intrinsic mathematical layouts such
as a matrix or piecewise function retain their mathematical rows inside the
formula. Formula-only Reading projections keep their independent layout.

Outside proof blocks, adjacent atomic facts, disjunctions and short chains may
flow in a paragraph separated by semicolons. Chains with at least three
relations use an aligned display. Equality chains continue at the equality
sign; mixed relations repeat each original adjacent left operand. Multiclause
predicates, guarded universals and existential assertions retain structured
rows. Bodyless theorems and sketches acquire no invented completion proof.

The document wrapper controls paragraph/display spacing and uses the existing
package set. The official reader renders the same compiler-owned paragraph and
formula boundaries; it does not flatten block output with CSS.

## Data flow and API

The CLI resolves `-latex` into `LaunchCommand::CompileToLatex { input:
LatexInput, language, document }`. `run_command` dispatches it to
`run_compile_to_latex` and returns `RunCommandOutcome::CompileToLatex` with a
`CompileToLatexResult`. Argument parsing and artifact JSON belong to the launch
and run layers; this compiler module accepts source or parsed AST values.
C/Python extraction uses the separate `ExtractExecutableCode` command and
`ExtractExecutableCodeResult`, retaining its verification requirement.

```text
source -> Tokenizer::tokenize -> Runtime::parse -> existing AST
       -> formula compilation + localized sentence compilation -> LaTeX
```

```rust
use litex::compile_to_latex::{to_latex_from_source, to_latex_document};
use litex::launch_command::OutputLanguage;

let fragment = to_latex_from_source("1 = 1", OutputLanguage::Chinese)?;
let document = to_latex_document(&fragment, OutputLanguage::Chinese);
```

`to_latex_from_ast(&[Stmt], &GlobalModuleManager, OutputLanguage)` renders an
already parsed batch. Module metadata is required because qualified names in
AST nodes carry module/export indices. Invalid indices fail explicitly instead
of printing placeholder names. The existing AST and Runtime structures are
unchanged. Crate-local `parameters_to_latex` and `fact_to_display_latex` also
let Reading reuse formula conversion directly. The display helper adds
structural breaks for ordinary unguarded quantified comparisons; other logical
forms retain the canonical formula and grouping. It does not alter document
compilation or execute/instantiate facts. The lower-level `to_latex(source, &mut Runtime)` retains the normal
parse API's successful bindings, but never publishes execution facts or defs.

Repository `-r` renders root `[export]` files in manifest order, with a section
heading for each export alias so local declarations have a visible namespace. Registered `-f`
renders the ordered root prefix through that file. An unregistered file renders
by itself, using the nearest enclosing manifest's naming metadata if present.
Dependencies are mounted from manifests only: their `.lit` files are neither
executed nor emitted. Same-path import aliases use the mount table's canonical
name; distinct modules with equal export/member names remain distinguishable.
Missing configs and import cycles fail before successful artifact output.

## Coverage and boundaries

| Source family | LaTeX representation |
| --- | --- |
| Numeric, set, function, tuple, template, struct/field objects | Mathematical notation, grouped operators, bounded domains and canonical names |
| Atomic/chain/and/or facts | Relations and logical formulae; parentheses only when a compound connective needs grouping |
| forall, forall-iff, exists, unique exists, negated quantifiers | Bound variables/carriers with preserved quantifier and connective scope |
| let/have/obtain/preimage/replacement | Localized introduction, choice and definition sentences |
| Functions by expression/cases/induction/unique existence | Function signature, equations, case arrays, measure and lower bound |
| prop/abstract prop/thm/axiom/strategy/struct/template/algo | Distinct labels and complete mathematical payloads |
| by cases/contra/enumerate/induc/strong_induc/for/extension/fn_extension/def/thm | Localized proof-method narration, goals, branches, explicit citations and nested bodies |
| release/expand/register/witness/claim/sketch/trust | Localized source actions, source-owned targets and explicit assumption/sketch labels |
| eval | Request to evaluate the expression; no computed value |

Dispatchers exhaustively match the current enums. Invalid source syntax fails
on the parse-only route. Malformed externally supplied chain/case/binding payloads also fail. Unknown
user predicates preserve their names and arguments; their meaning is not guessed.
Comments and quoted asides are already discarded by the tokenizer and are not
recovered. A bodyless theorem is rendered without an invented proof. Very long formulas
and case arrays can exceed page margins; automatic line breaking or whole-book
pagination is not provided. These output fragments remain editable LaTeX.

The primary tracer is
[`identity.lit`](../../examples/stmt_nodes/compile_to_latex/identity.lit): before
this module there was no current `-latex` route; it now renders a named theorem
followed by an explicit selected theorem citation. False facts such as `1 = 2`
remain convertible, whereas invalid syntax fails with no successful partial
content. Those boundary inputs live in conversion tests, outside the ordinary
positive verification examples.

The layout tracer is
[`structured_proof_layout.lit`](../../examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit),
a checked positive-integer proof combining cases and contradiction. It retains
the original mathematics while replacing repeated proof captions and displays
with a single proof and distinct branches. The earlier generated
[Chinese PDF](../../examples/stmt_nodes/compile_to_latex/structured_proof_layout.zh.pdf)
and [English PDF](../../examples/stmt_nodes/compile_to_latex/structured_proof_layout.en.pdf)
have editable `.tex` companions and preserve the earlier layout snapshot;
use the current compiler or `-reading -latex` for the connected prose.
Parameterized structures without additional
guards use a plain introduction, avoiding empty `$$` math in conditional prose.

## Per-type format contract

[FORMATS.md](FORMATS.md) assigns a layout or mathematical notation to every
current leaf: 52 statement types and 150 object types. The maintained
[machine catalog](../../tests/fixtures/compile_to_latex/format_catalog.json)
also exercises five application-head forms, five limit directions and all ten
logical fact shapes. These 222 specimens are parse-only format examples;
their parser context is not a mathematical verification certificate.

`catalog_kinds.rs` exhaustively classifies the actual AST variants. Catalog tests
compare the exact declared type sets, parse each specimen, check its actual
variant, and render it through the production compiler. New variants, omitted
rows, duplicate rows and samples of the wrong type fail.
Statement fragments are selected using exact compiler-owned spans in their
original context, so a nested proof's inline typography is retained; each
selected fragment must occur byte for byte in the full compiled source.
A separate operand retention check uses unique sentinels for every matrix and multivariable
selector argument, including explicit dimensions. Export the compiler-owned
specimens for a native rendered gallery with:

```sh
LITEX_LATEX_CATALOG_OUTPUT="$PWD/tmp/latex-catalog.json" \
  cargo test --release --lib compile_to_latex -- --nocapture
```

Matrix notation is selected by the individual operation: transpose, Hermitian
transpose, determinant, trace, products, minor submatrices, cofactors and norms
have separate formats. Bracketed size tags such as `[m,n]` retain source
dimension operands and are not matrix-entry subscripts. Fibre preimages use
`f^{-1}[{y}]`, while set preimages use `f^{-1}[S]`. Generated summation and
integration variables preserve the original functions and bounds.

The [per-type acceptance report](../../tests/fixtures/compile_to_latex/all_types_acceptance.json)
records the current exhaustive coverage, real CLI/native typography checks,
and the separate verified source/evidence hover tracer. The native gallery
checks each exported full fragment byte for byte against the actual CLI,
then renders the unchanged selected fragment with XeLaTeX. Gallery samples
and verified proof evidence have separate provenance.

## Focused validation

```sh
cargo test --release --lib compile_to_latex -- --nocapture
cargo test --release --lib launch_command_tests -- --nocapture
cargo test --release --lib latex_command_tests -- --nocapture
cargo test --release --test compile_to_latex_cli -- --nocapture
cargo test --release --test reading_latex -- --nocapture
node src/reading/web/tests/latex-mode.cjs --compiler target/release/litex
cargo build --release
target/release/litex -f examples/stmt_nodes/compile_to_latex/identity.lit
```

Unit coverage converts every current statement fixture in all ten
languages, exercises the maintained object corpus, and checks grouping, logical
scope, escaping, assumptions and unchanged execution stores. CLI tests check the
actual binary, all language/document modes, error envelopes, manifest order,
file-prefix selection and module identity; intentionally invalid dependency
source demonstrates that imports are not executed. Generated document syntax,
fonts and typography are checked separately with XeLaTeX.

Connected prose has an exact bilingual regression in
`proof_prose_connects_assumptions_steps_and_structural_conclusions`.
Reading contracts compare compiler bytes and native evidence in all ten locales.
The live shared-viewer check renders all 52 statement fixtures in memory and
checks that the joined case's transition word still belongs to its original
proof-body statement, with unchanged source/proof navigation.

The optional native typography gate converts the current statement and
object fixtures in every locale and rejects TeX errors or missing glyphs:

```sh
python3 tests/compile_to_latex_xelatex.py --output-dir tmp/2026-10-06/compile-to-latex/tex-gate
```

The dated [acceptance report](../../tests/fixtures/compile_to_latex/acceptance.json) records the focused gates, binary checksum, typography results and environment limits. The [Chinese example document](../../examples/stmt_nodes/compile_to_latex/identity.zh.tex) and [rendered example](../../examples/stmt_nodes/compile_to_latex/identity.zh.pdf) show the primary tracer.

The [layout redesign acceptance](../../tests/fixtures/compile_to_latex/layout_redesign_acceptance.json)
records the 2026-11-01 layout checks: 18 optimized production-module tests,
7 real CLI release tests, and all 52 statement / 106 object fixtures compiled
in all ten locales. It also records the unrelated concurrent Lean interface
error that blocked the subsequent whole-crate Cargo build/unit attempts.
Overfull warnings for very long formulas remain outside the typography gate.

The [command separation acceptance](../../tests/fixtures/compile_to_latex/command_separation_acceptance.json)
records the 2026-10-07 parser, dispatcher, Runtime provenance and real CLI
checks: 50 focused release tests passed, and all 22 saved artifact envelopes
(ten locales in both fragment/document forms, plus C/Python) remained identical.

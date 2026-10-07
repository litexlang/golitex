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

The CLI emits one JSON artifact. Its stable keys include `success`, `format`,
`target`, `path`, `language`, `verified`, `content`, and `error`. `success` means
conversion succeeded; `verified` is always false. On failure, `content` is null,
`error` describes the source/config/conversion error, and the process exits 1.
`-session` and `-strict` do not apply to this conversion route.
Invalid launch arguments use the common CLI diagnostic path: stderr and exit 2.

Save a complete document without copying JSON escapes:

```sh
litex -latex -document -lang zh -f example.lit | python3 -c 'import json,sys; a=json.load(sys.stdin); sys.exit(a["error"]) if not a["success"] else sys.stdout.write(a["content"])' > example.tex
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
display math, case arrays, and scoped proof quotations. `-document` (or the Rust
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
unchanged. The lower-level `to_latex(source, &mut Runtime)` retains the normal
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
| Atomic/chain/and/or facts | Relations and explicitly scoped logical formulae |
| forall, forall-iff, exists, unique exists, negated quantifiers | Bound variables/carriers with preserved quantifier and connective scope |
| let/have/obtain/preimage/replacement | Localized introduction, choice and definition sentences |
| Functions by expression/cases/induction/unique existence | Function signature, equations, case arrays, measure and lower bound |
| prop/abstract prop/thm/axiom/strategy/struct/template/algo | Distinct labels and complete mathematical payloads |
| by cases/contra/enumerate/induc/strong_induc/for/extension/fn_extension/def/thm | Localized proof-method narration, goals, branches, explicit citations and nested bodies |
| release/expand/register/witness/claim/sketch/trust | Localized source actions, source-owned targets and explicit assumption/sketch labels |
| eval | Request to evaluate the expression; no computed value |

Dispatchers exhaustively match the current enums. Retained but parser-retired
cart/tuple dimension/projection objects and shape predicates fail explicitly.
Malformed externally supplied chain/case/binding payloads also fail. Unknown
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

## Focused validation

```sh
cargo test --release --lib compile_to_latex -- --nocapture
cargo test --release --lib launch_command_tests -- --nocapture
cargo test --release --lib latex_command_tests -- --nocapture
cargo test --release --test compile_to_latex_cli -- --nocapture
cargo build --release
target/release/litex -f examples/stmt_nodes/compile_to_latex/identity.lit
```

Unit coverage converts every one of the 50 current statement fixtures in all ten
languages, exercises the maintained object corpus, and checks grouping, logical
scope, escaping, assumptions and unchanged execution stores. CLI tests check the
actual binary, all language/document modes, error envelopes, manifest order,
file-prefix selection and module identity; intentionally invalid dependency
source demonstrates that imports are not executed. Generated document syntax,
fonts and typography are checked separately with XeLaTeX.

The optional native typography gate converts the 50 statement fixtures and 94
object fixtures in every locale and rejects TeX errors or missing glyphs:

```sh
python3 tests/compile_to_latex_xelatex.py --output-dir tmp/2026-10-06/compile-to-latex/tex-gate
```

The dated [acceptance report](../../tests/fixtures/compile_to_latex/acceptance.json) records the focused gates, binary checksum, typography results and environment limits. The [Chinese example document](../../examples/stmt_nodes/compile_to_latex/identity.zh.tex) and [rendered example](../../examples/stmt_nodes/compile_to_latex/identity.zh.pdf) show the primary tracer.

The [command separation acceptance](../../tests/fixtures/compile_to_latex/command_separation_acceptance.json)
records the 2026-10-07 parser, dispatcher, Runtime provenance and real CLI
checks: 50 focused release tests passed, and all 22 saved artifact envelopes
(ten locales in both fragment/document forms, plus C/Python) remained identical.

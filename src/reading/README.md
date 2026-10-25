# Interactive textbook reading

This module is the home for turning Litex source and its verification evidence
into an interactive textbook. A reader should be able to select a statement,
inspect the grounds actually used to establish it, and follow those grounds
back to facts, definitions and rules. Concept highlighting follows resolved
symbol identity, separately from proof dependencies.

## Current status

The initial implementation provides a typed reading projection, a shared
browser viewer, loopback preview/upload, JSON output and static export.
It reads actual execution results; it does not reconstruct dependencies from
localized verifier messages or search for a different proof.

```sh
litex -reading
litex -reading -f chapter.lit
litex -reading -r book/
litex -reading -json -f chapter.lit > chapter.reading.json
litex -reading -export book-site -r book/
```

For a complete mathematical demo, use
`litex -reading -strict -lang zh -r examples/reading/homepage`.
The [homepage collection](../../examples/reading/homepage/README.md) includes
least squares, sets, Newton iteration, irrationality of √2 and Cantor's theorem.

Preview opens a browser; `-no-browser` prints the URL without opening one.
Use `-port 49181` to choose a port, `-lang zh` for Chinese presentation and
`-strict` to use the verifier's strict execution policy. File/project inputs
use the existing project loader. `-e` uses isolated source evaluation.
Bare preview accepts `.lit` files, a complete project folder, or an existing
reading JSON bundle. A dependent source needs its project configuration and
dependencies. The local service listens only on `127.0.0.1`.

The viewer follows the typography and palette of `../litex-webpage`: a light
background, green controls, blue current statements, green cited facts and
purple concepts. A selected `prop` shows its full predicate application, then
⇔ beside a grouped block containing every argument type and all complete
defining conditions. Short clauses share a row, with each conjunction kept
with its following clause; longer formulas retain their mathematical layout.
Repeated instantiated conditions retain their separate fact links. There is
no prose or separate domain heading. This is the
reading form of the declared typed interface; quantified conditions retain
their whole scope. Click the source keyword `prop` for the
purpose/semantics guide and its checked short example. Source keyword help
supports Enter/Space; Escape returns focus to its keyword. A new statement
selection restores mathematical content. The right pane’s type caption is plain
text. Usage hints, the color legend and record explanation live in the footer’s
Reading help disclosure. Small file-local reference counts appear at every explicit declaration;
its occurrence list starts closed. Hover/focus uses resolved definition spans
and typed parameter evidence to show the exact binding line and declared domain,
including quantified parameters and shadowed names. Later inferred memberships
do not replace that domain; missing evidence does not trigger a text guess.

The detail pane omits duplicate source, engine versions, file/line metadata,
proof trees and a default rule catalogue. Source concepts and real fact
citations remain clickable. Preview, static export and embedding share this
viewer without a Node runtime or frontend build. Bundled KaTeX and embedded
WOFF2 fonts work offline; see web/vendor/katex/README.md for version/license
and deterministic regeneration. Rendering disables trusted HTML/URL commands.

Reading controls use a closed “Reading records” disclosure instead of visible
JSON import/download buttons. The primary action is “Open a file”; there is no
download control. It explains that records save how each statement
was checked, which facts it used and what it inferred; JSON is described as the
file format. Folder opening, when available, stays inside. The chapter directory starts closed,
and Back appears after navigation. The shell supplies optional `onOpenFiles` and
`onOpenProject` callbacks; the shared component owns the controls. File inputs and upload validation remain shell responsibilities.

Optional schema-v2 `statement_kind` retains the real tagged AST path. Optional
`declaration_symbol_ids` identifies direct named declarations using captured
typed fields, excluding function parameters and nested binders. Definition-line
badges show current-file source references. Clicking a badge lists source
snippets and jumps to the exact token. Counts use resolved symbol identities
and unique UTF-8 spans, excluding the declaration itself and generated inferred
output; comments are not symbol occurrences. Repeated execution does not inflate
the count. These are source references, not proof-dependency counts.
The concept occurrence list also uses original source snippets and marks the
exact token, rather than showing execution-resolved mathematical subjects with
internal file qualifiers. Clicking navigates to that token. Authored qualified
names stay unchanged. For an unloaded chapter, its symbol name and source path
remain navigable until the chapter is loaded.
Optional `mathematics` display data comes from typed AST values and retained execution
results. Optional `mathematics.latex` contains a `subject` formula and parallel
`parameters` and `facts` arrays generated by the existing LaTeX compiler. Missing/unsupported conversion
keeps the complete retained text; it never reparses source or guesses formulas.
Ordinary quantified comparisons use structural display breaks; other logical
forms preserve the canonical compiler grouping and may scroll horizontally.
The viewer left-aligns the outer gathered comparison layout, groups parameter
commas with their formula, and aligns conjunctions beside complete clauses.
A simple two-row outer comparison without nested environments can flow inline,
so short inequalities stay on one line. Matrix/case layouts keep their original
grouping. Plain-text fallback never breaks an identifier in the middle.
Parameter-type metadata stays distinct from iff-clause metadata; the viewer
places both in the right-hand condition block of the typed predicate display.
Instantiated equivalences retain every complete definition clause, including
conjunctions and chains; they are not reconstructed from a filtered list of
published inferred outputs. Abstract predicates receive no invented definition.
The current projection covers ordinary predicate definitions/applications,
selected object declarations, function equalities and fact goals. Other forms
show actual recorded output facts where available, or an explicit unavailable
message. Older bundles remain readable without guessed mathematical meaning.
Clicking source selects the statement; result/citation buttons select the fact.

Source ranges use original UTF-8 byte offsets. Syntax highlighting distinguishes
keywords, predicates, functions, objects/variables, types/sets, theorem names,
numbers/constants, operators, punctuation and comments/asides. Resolved symbol
identities, declaration kinds and typed function-head evidence determine semantic
colors; source spelling never overrides a resolved identifier. Declarations and
uses share their role. Selection/citation highlights retain priority.
`python3 src/reading/generate_highlighting.py` refreshes the inline lexical
catalogue from parser constants, analysis-property dispatch and tokenizer symbols;
`--check` detects stale vocabulary. No extra browser asset or frontend build is
required. Tokens without a specific authored explanation receive concise role
help where appropriate. Builtin set
help (for example `R`: real numbers ℝ) is keyed by resolved symbol identity,
not spelling. Tooltips support Escape and stay inside the viewport. Optional
source `tokens` records normalized tokenizer text with original UTF-8 ranges;
comments and inline asides are excluded, Unicode aliases retain their original
source spelling, and lazy exports load tokens with the chapter. Tokenization
failure leaves plain source; older bundles retain resolved-set help without
inventing lexical boundaries. This is language help, not mathematical proof
evidence. Occurrence highlighting uses resolved identities and reports mapping coverage per statement. Typed proof
payloads and retained local scopes are exported. Actual store/infer outputs
link seed facts to derived fact IDs; the reader displays one compact grey count
button beside each producing statement on the same source line, excluding temporary
definition/parameter-checking assumptions, and can follow a later citation
back to an inferred fact. Clicking the button opens an anchored popup containing
the actual results; clicking it again, clicking outside or pressing Escape
closes the popup. Escape restores button focus. Result text wraps within the
popup and stays hidden by default; the source gains no display rows.
Selecting an inferred output shows the producing predicate's complete
mathematical equivalence when retained, highlighting the selected domain or
condition. Named definition links lead to that definition's mathematical view.
Trust, failures and local-scope qualifications remain visible. Full execution
evidence and per-conclusion origins remain in JSON; optional language help
provides access to the Rule Book.
Nested proof statements
and repeated execution contexts retain separate identities. Ordinary facts
have exact source focus and hypothesis/verified/declaration roles. Actual WD
registrations and their retained formation evidence are navigable. Whole-book
exports load source/proof chapters, search and concept indexes on demand;
complete JSON and a standalone offline page remain available. The loopback
service caches identical successful closed-project uploads in bounded memory.
Rule descriptions are shown when authored metadata
is available; a catalogue entry alone is not a complete mathematical rule
specification. [DESIGN.md](DESIGN.md) records the full target and acceptance
boundaries; this first implementation does not establish every target there.

## Website embedding

See the [integration guide](../../docs/reading.md) for schema v2 evidence DAGs,
inference records, the local upload API, component methods and iframe messages.
The [runnable host example](../../examples/reading/website/README.md) uses the
same export through both integration paths.

Publish the generated `book-site/` files alongside the website, then embed the
published page:

```html
<iframe src="/books/book-site/index.html"
        title="Interactive textbook"
        style="width:100%;height:85vh;border:0"></iframe>
```

Or load `katex.min.css` and `reader.css`, then `katex.min.js` before
`reader.js`, and mount the viewer into an existing element. Its styles are scoped to the reader; standalone page styles require
the `litex-reading-page` body class.

```js
const reader = await LitexReading.open(document.getElementById('reader'),
  '/books/book-site/reading.manifest.json', { locale: 'zh' });
```

Static browsing uses the exported evidence and needs no running Litex process.
The loopback preview URL belongs to the local machine; publish the export to
make it available to website visitors. Rechecking edited source requires a
separate execution endpoint; mounting the viewer does not install one.

## Ownership

The reading subsystem owns the exported reading model, its projection
from checked results, source/occurrence mappings, rule catalogue export,
and the reusable browser viewer and its assets. Local preview and published
websites should consume the same model and viewer.

Existing components retain their responsibilities:

- [run](../run/README.md) and [run_module](../run_module/README.md) load and
  execute sources in their real project context.
- [execute](../execute/README.md) and
  [store_fact_and_infer](../store_fact_and_infer/README.md) produce typed
  verification, storage and inference evidence.
- [json_output](../json_output/README.md) retains its current Normal, Compact
  and Detailed contracts. Reading is a separate projection of the typed
  evidence, without decoding localized JSON or replacing the evidence owners.
- [identifier_identity.md](../identifier_identity.md) defines symbol identity;
  [TokenBlock](../tokenize/token_block.rs) retains original token byte ranges.

CLI dispatch in the existing launch/run layers delegates reading work here.
Reading must preserve statement transactions,
scope visibility, source order and explicit trust boundaries.

## Maintaining the projection and catalogue

```sh
python3 src/reading/generate_capture.py
python3 src/reading/generate_capture.py --check
cargo test --release --test reading --test reading_http
```

The generator reads typed Rust evidence and authored rule metadata. Exhaustive
enum matches and full struct destructuring make newly added fields/variants
an explicit regeneration obligation. Keep `rule_ids.json`: it preserves
stable rule identities independently of localized names. Do not maintain a
second rule list in the website or construct fake proof instances for metadata.

Source labels: optional `reading-titles.json` files beside actual sources own
Chinese/English example names. Capture validates and copies `sources[].titles`;
partitioning preserves these fields in manifests and chunks. The shared viewer
renders labels with text content and keeps the original path as identity.
The upload bridge admits only this additional presentation filename, includes
it in request cache identity and passes it through to child verification.

Builtin numeric hover cards in `web/reader.js` follow the scalar WD domains
in `execute_fact_stmt/well_defined_results/verify_obj/scalar.rs` and object
semantics in `ast/obj.rs`. They are language-reference documentation, not
expression inference. The 31 illustrative equalities were checked together
with strict release CLI verification (2026-10-24). Missing entries retain
generic help; resolved user symbols take precedence. With a checking host, all examples now open directly in the shared editable IDE
with grey inference buttons and resolved hover, using the same reading service. Changed text immediately clears old verification/evidence from
the view; rejected statements are marked red after checking. Pending draft coloring is lexical only; semantic hover and real inferred
FactIds return after checking. There is no separate reading/editing mode. Static
exports need a host checking callback or endpoint to enable editing. See
[Editing and checking](../../docs/reading.md#editing-and-checking) for the
callback, single-configuration project scope and local gallery proxy.

Optional host-authored `exampleGroups` add bilingual links to independent
reading bundles in the existing Examples menu. `includeSources: true` merges
the current chapters into the matching category without duplicates. The gallery
uses Passes / Does not pass categories. The shell reads them from an
optional JSON script `reading-example-groups`; only relative directory links
are rendered, and locale is propagated across navigation. This does not extend
the proof schema or merge failure bundles into a successful collection. See
`examples/reading/homepage/export_gallery.py` for the reproducible builder.

### Stable inspector and reference cards

The inspector has a viewport-scaled fixed height, independent of the selected
statement. Its content scrolls internally, including long proof grounds. The
editor remains editable when a source token is clicked to inspect its help.

Authored builtin reference cards are shared by hover and click. Numeric cards
state input restrictions and results (for example `+` takes two complex numbers
and returns a complex number). Set operators such as `union`, `intersect`,
`set_minus`, `power_set` and family/indexed variants are explicitly labeled
**Set operator**. Their inputs are set-kind requirements, never a fabricated
universal set domain. Indexed union/intersection require nonempty indices in
the current verifier. These cards describe builtin contracts, not an inferred
type of the selected expression; resolved user declarations keep their own help.

Detailed keyword cards currently cover `prop`, `by def`, `forall`, `claim`,
`have fn` and `by contra`: summary, syntax, behavior/restrictions and a runnable
example. Other existing keyword hints remain concise. Numeric cards cover
arithmetic, real elementary/trigonometric/hyperbolic functions, integer
operations and complex parts/modulus; this is not exhaustive builtin coverage.
The format borrows summary-plus-detail from Python PEP 257 and the synopsis,
parameters/results and examples structure from Linux man-pages(7).

The `prop` and `by def` cards explain the shared `nonnegative(x R)` example
point by point. The expanded reference distinguishes formal parameter type,
predicate meaning, the complete defining equivalence, declaration versus
instance, and proof by substitution. Its equivalence is rendered with the
shared local math renderer, with complete text fallback. Hover retains the
compact reference and example, linking the reader to the full explanation by
clicking the source keyword. Detailed content scrolls inside the fixed panel.

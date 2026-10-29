# Interactive textbook reading

**The source is the textbook and the primary reading interface.** Definitions,
mathematical statements and proofs are expressed in Litex source, with inferred
facts displayed beside the statements that produce them. Definitions, parameter
domains and proof references are accessible by interacting with that source.
Readers do not need to open a separate Info View to follow the mathematics.
Explanations and proof grounds open on demand beside the selected source.
There is no standing mathematical-meaning pane; readers close the contextual
explanation to return to the unobstructed source.

This module connects the source to its actual verification evidence, so readers
can follow citations back to facts, definitions and rules. Concept highlighting
follows resolved symbol identity, separately from proof dependencies.

Hover anywhere in a mapped fact's source row for a transient proof preview;
focusing its line number provides the same keyboard access. The sentence owns
the initial dwell timer and proof content: moving between its tokens neither
restarts that timer nor rebuilds the proof. Hovering an object, predicate,
operation or keyword adds a separate symbol-information compartment to the same
preview. Changing symbols preserves expanded proof conditions and scroll
position. The last symbol information remains available while entering the
card; both compartments scroll independently and stack on narrow screens.
Entering the card cancels delayed dismissal and incidental pending previews
from crossing neighboring sentences. Outside facts, symbols retain standalone
semantic help. Definitions and proofs still follow their separate recorded
identities; hovering an object does not select it as the conclusion.
The preview follows that primary fact's own evidence and exact source line,
including conclusions nested inside a larger proof. Its premise links navigate
to actual FactIds. Symbol help uses the same renderer inside and outside proofs.
Mathematical premises are visible first; parameter and expression conditions
remain available in a disclosure. Verified chains expose their adjacent steps
from the recorded result, rather than treating the enclosing statement's entire
citation list as the proof of each line. Hypotheses are labeled as hypotheses.
Moving away, Escape, editing, navigation or closing the preview dismisses it.
Unchecked or unmapped lines do not receive guessed proof evidence. Missing
fact-specific proof steps are stated explicitly; authored summaries currently
cover selected proof forms, not every kernel rule. JSON remains the underlying
evidence format; the reader has no raw JSON column or JSON-view toggle. Source
hover and on-demand explanations expose definitions, citations and inferred
results directly beside the mathematics.

Proof explanations connect their cited context with the actual rule application.
The rule's exact recorded name is visible, together with its catalogue statement
when available. Builtin strategies and structural membership derivations retain
their own names and categories. For example, `p / 2 $in Z` in the sqrt-two lesson
uses `ExactIntegerDiv`: the context supplies integer membership and divisibility,
and enclosing expression verification owns the nonzero-denominator requirement.
The card gives the guarded integer-quotient law and the substitution `a = p,
b = 2`. It does not claim that the distinct `ExactIntegerQuotient` fallback was
called. Application selection follows the current proof's typed wrapper chain,
not a recursive collection of rules from premises, WD or earlier statements.
Consequently each equality step retains its own rule. Missing catalogue text
does not erase a retained application name; catalogue presence alone does not
establish an application. Assumptions and rejected statements receive no
successful-rule label. Hover and pinned views use the same formatter.

Atomic proof applications expose four complementary routes. Known-fact reuse
links the precise cited fact and pairs its arguments with the current arguments
using the recorded equality certificates; changed arguments are visible by
default. Builtin rules and builtin strategies show their actual name, retained
requirements and current conclusion. A `forall` application identifies the exact
universal fact, lists parameter substitutions in declaration order, and presents
the already-instantiated premises with their matching proofs. Parameter domains
and conclusion-argument matching remain available separately. The viewer never
substitutes source strings to construct those premises.

Named strategies show the recorded strategy name and bindings recovered from
typed parameter identities and argument-match records. They do not acquire a
guessed definition link: current detailed records do not retain a resolved
strategy-declaration identity. Missing parameter lists, unmatched proof identities
or incomplete records receive explicit explanations rather than invented
correspondences. Reference navigation and return retain the selected application.

Equality operators have their own proof targets when retained evidence maps
them precisely. In `a = b = c`, hovering the first `=` explains only `a = b`;
the second explains only `b = c`, with that step's own mathematical citations
and parameter conditions. Focus or click the operator to inspect it, or use
the preview's **Keep open** action; in the editable overlay, Ctrl/Cmd-click
selects that step while ordinary clicks still position the text caret. Normal
line selection returns to the complete chain. Source rows and inferred results
are unchanged.

The binding uses `VerifyChainFactSuccess.adjacent`, `ChainFact.objs` and
`prop_names`, the same adjacent verification results read by Normal JSON's
chain projection. Exact tokenizer byte spans locate the source operators;
nested parentheses, brackets, braces and tokenizer-excluded comments do not
consume chain positions. The complete top-level operator sequence and typed
operand identities must agree. A supported standalone verified equality uses
its own `VerifyEqualitySuccess` in the same way. Multiple possible primary
facts, missing evidence/tokens, mismatched counts or identities, and unsupported
multiline/nested source mappings receive no guessed operator proof. Existing
whole-chain previews and language help remain available. Some proof forms
still have only a general explanation plus retained citations.

For example, syllogism fact `f5` cites universal fact `f4` and hypothesis `f1`;
domain condition `f9` remains separately accessible in the proof preview.
Captured statements inside `by contra` keep their individual source identity
and evidence. The sqrt-two goal and terminal `impossible` do not currently have
independent statement records; removing the raw view does not add evidence for
unmapped lines or change the underlying reading JSON/export contracts.

Quantified fact references use retained `ForallFact` and `TypedParameterGroup`
structure to render their binders in natural language: Chinese uses
`对于任意集合 X`, `对于任意非空集合 X`, and `对于任意有限集合 X`;
English uses `For every set X`, `For every nonempty set X`, and
`For every finite set X`. Ordinary domains retain membership, such as
`对于任意 x ∈ ℝ` / `For every x ∈ ℝ`. Source keeps the keyword `forall`.
Grouped names, dependent domains,
nested scopes, premises and conclusions are preserved. English uses set-kind
annotations in English. Missing or unsupported structure keeps the complete
original formula instead of guessing a quantifier header from its text.

Proof previews show concrete universal instantiations when the retained proof
contains an ordered argument list and its cited quantified fact. For example,
the syllogism displays `person = socrates`; the same component displays
`a = 72, b = 84, c = 96` in the least-squares example. Incomplete metadata or
an arity mismatch retains the general explanation rather than inventing a
substitution. Hover and selected-source views use the same proof content.
The preview's **Keep open** action fixes that explanation beside the source.
Fact line numbers indicate this entry point; keyboard users can focus a line
number and use Tab or Right Arrow to enter its open preview.

Grey inline inference buttons preview one complete retained result and show
the number of additional results. Visual ellipsis does not shorten the stored
formula, remove clauses or discard FactIds: opening the button shows every
published result. The source retains its original rows. Supported generated
existential facts use fresh local mathematical witness names, such as `k`,
instead of internal binder names. This display-only substitution uses retained
symbol identities, avoids free and bound names, preserves existence/unique
existence/nonexistence, and leaves authored source names unchanged. Ambiguous
identities or unsupported structures retain the complete original formula.

Local facts identify their recorded enclosing proof and distinguish assumptions
from conclusions established under those assumptions. Current scope metadata
does not identify every nested lexical range; the viewer does not invent scope
brackets from indentation. These are shared reader behaviors, independent of
problem-specific commentary or exercises.

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
selection restores mathematical content. The contextual explanation’s type caption is plain
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
In the editor, an ordinary click only positions the caret and selects context;
Ctrl/Cmd-click performs the token's semantic action or keeps its explanation open.

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

HTTP responses include their exact byte length. After writing a response, the
connection closes its write side before draining unread request bytes with a
250 ms deadline and a 16 MiB limit. This lets early upload rejections deliver the complete
error response without a TCP reset discarding it. No further request on that
connection is processed. `tests/reading_http.rs` checks complete responses for
rejected uploads with 64 KiB bodies, alongside normal uploads and strict policy.

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
Items may provide language-specific `hrefs` alongside the existing `href`
fallback. The bilingual source lessons use these paths and standard same-origin
alternate-page metadata. The shell changes the authored source language only
when the original document is still open and `hasLocalEdits()` is false;
otherwise it preserves the source and changes the interface language. This
read-only component query includes checked edits that differ from the initial
text. No additional draft owner or per-example renderer is introduced.

`ReadingSite` writes optional source-only parts alongside the existing proof
chunks. Manifest `source_url` points to a `reading_source` envelope with the same
snapshot identity and a token-free source record. The shared loader validates
snapshot, source ID, path and text type, then caches only the text for
`getProjectSnapshot()`. Preparing input does not merge these parts into the
viewer or make unloaded proof available. Navigation retains its independent
full-chunk path. Older exports fall back to that path for source snapshots;
failed source loads retry and document changes invalidate pending snapshots.
This is an additive packaging capability, not a reading-proof schema change.

Upload checking uses a streaming JSON whitespace compactor between the child
CLI and the existing bounded output file. It preserves all string bytes and
field order, including the source and proof records. The unchanged 256-MiB
limit measures compact transport; the CLI's formatted JSON contract is unchanged.
Resource failures reap the worker and join its output collector before workspace
cleanup. This is transport handling, independent of capture, verification and
source-only loading. Pure streaming tests and real loopback/cache tests cover
the format and service boundaries.

The maintained `web/tests/host.cjs` acceptance runs the unmodified page shell
and reader against actual exported parts and actual strict CLI checks. It
covers a rejected predecessor, later unchecked chapters, restoration, keyboard
checking, and navigation while a result is pending. Working-copy edits clear
semantic selections immediately; rendering that draft does not cancel chapter
navigation. Restoring unchanged text is a no-op. The iframe bridge requires a
nonopaque parent origin and current bundle identity; disposed readers reject
new work. These component/CLI checks remain separate from browser layout
acceptance; see `web/tests/README.md`.

### Contextual explanations and reference cards

Predicate hover presents definition and proof together. Both use retained typed
data: the resolved declaration and complete predicate display, then the actual
verification record and its requirement/proof pairs. The builtin-rule and
strategy routes for intersection membership both expose the two member-set
proofs. Finite-set membership/non-membership explain the retained equality or
disequality certificates. Proof conditions expand on demand and must match
their evidence's fact identity; mismatched records remain unavailable.

Older bundles may attach accepted `by def`, `by thm` or `by contra` evidence only
to the execution result. The reader derives local display metadata from those
exact success variants, without modifying the bundle, allocating facts or
changing verification. Contradiction goals and local negation assumptions keep
their distinct roles. Current failed statements can show their definition and
check failure together. Unknown definitions and proof forms remain explicit.

The source occupies the full reading width. A contextual explanation opens
only after a source interaction, stays within the viewport and scrolls internally
when necessary. Close it with its close button, Escape or an outside click.
Changing examples closes it. The editor remains editable when inspecting help.
Pinned equality explanations stay at the selected relation operator. All
source cards dismiss when their owner leaves the editor's visible rectangle,
including horizontal scrolling; they do not remain detached from their source.

Authored builtin reference cards are shared by hover and click. Numeric cards
state input restrictions and results (for example `+` takes two complex numbers
and returns a complex number). Set operators such as `union`, `intersect`,
`set_minus`, `power_set` and family/indexed variants are explicitly labeled
**Set operator**. Their inputs are set-kind requirements, never a fabricated
universal set domain. Indexed union/intersection require nonempty indices in
the current verifier. These cards describe builtin contracts, not an inferred
type of the selected expression; resolved user declarations keep their own help.

Detailed keyword cards currently cover `prop`, `by def`, `forall`, `claim`,
`have fn`, `by contra` and `release thm`: summary, syntax, behavior/restrictions and a runnable
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
clicking the source keyword. Detailed content scrolls inside the contextual explanation.

Theorem highlighting follows retained `TheoremCall` symbol references, not
name spelling. A retained resolved `Builtin` callee marks builtin theorem
identity; ordinary user theorems and mathematical objects remain distinct.
`release thm` has a shared hover/click reference explaining argument
instantiation, parameter-domain and premise verification, and publication of
all theorem conclusions. Its checked prime-divides-power example uses the
actual `(a, k, p)` parameter order. Builtin theorem cards currently give
mathematical statements for prime-divides-power and unique reduced fractions;
other builtin theorem names retain an honest category description.

Unique existence `exist!` is one highlighted/help span even when retained
lexical tokens split `exist` and `!`. The reader also accepts horizontal spacing
between these tokens, matching the parser. Its hint states existence and
uniqueness together; ordinary `exist` retains its existential hint and a
factorial `!` is not absorbed into a quantifier.

Builtin rule comments are produced by the owning proof type's
`rule_name_and_message_en` / `_zh` methods. Reading captures both languages on
**each actual rule application** as optional `comment.en` / `comment.zh`
`{name, message}` objects. This preserves different laws within one catalogue
family and supports language switching without rerunning a proof. The catalogue
remains the fallback for older exports. Adding a builtin family without a comment
owner fails the capture generator; a new variant must also satisfy the owner's
exhaustive Rust matches. New disjunction/existence comments currently cover
English and Chinese, with English fallback for other output languages.

Every retained successful atomic verification, including each adjacent equality,
ends with a closed **Well-defined expressions** disclosure. It reads only that
verification's WD certificate, retains its actual verified domain conditions and
proofs, and stops before walking into a condition's own proof. Each condition
opens its own explanation, with its own WD disclosure at the end. Closed numeric
conditions such as `2 != 0` remain inspectable. This presentation never changes
WD ownership, proof search, fact identities or verification order.
If atomic proof search fails after WD succeeds, the rejection explanation keeps
that same closed WD tail. A successful domain check never marks the goal proved;
a failure during WD continues to show its unmet condition as the diagnostic.

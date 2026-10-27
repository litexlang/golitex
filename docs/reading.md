# Interactive Litex reading

Reading exports the verification evidence of a Litex file or project. The
same JavaScript reader uses that JSON in a local browser or a hosted webpage.
The source occupies the reading area without a standing explanation pane.
Hover for semantic hints; click source, definitions or inferred facts for a
contextual explanation beside the source. Close it with ×, Escape or an outside
click; long content scrolls inside. These explanations share statement IDs,
fact IDs, resolved symbol identities and actual verifier citations with the
source. Switching examples or editing source closes old explanations.

Theorem roles follow typed theorem-call records. A resolved builtin callee is
labeled **Builtin theorem**, while a user theorem remains **Theorem**.
`release thm` hover explains instantiation, verification of parameter domains
and premises, and introduction of every resulting conclusion.

Hover a fact predicate or the blank area of its source row to preview its proof.
Focus the line number for keyboard access. Premises are clickable and highlighted
in the source; the preview stays open while the pointer is inside it. It uses
the selected primary fact's recorded evidence, including nested conclusions,
rather than the citations of the whole enclosing proof. Parameter and expression
conditions are available separately. A chain offers its recorded adjacent
relations as individual steps. Hypotheses remain explicitly conditional, and
unchecked edits immediately lose their old proof previews. Some proof forms
still lack an authored explanation; missing evidence is never reconstructed
from matching source text. The JSON supports this interaction without appearing
as a separate output panel.

For real mathematical examples, run
`litex -reading -strict -lang zh -r examples/reading/homepage`.
The [homepage collection](../examples/reading/homepage/README.md) contains
least squares, sets, Newton iteration, irrationality of √2 and Cantor's theorem;
use the top-right example menu to switch between them.

## Semantic hover hints

Hover or focus an object name for its concise role, declaration and scope.
Common builtin numeric operations have authored bilingual reference cards with
surface syntax, domain/range, meaning and a checked example. The current 31
entries cover arithmetic, powers, integer operations, elementary real functions,
inverse trigonometric functions and complex parts/modulus. These cards describe
the language operation, not a computed type for this particular expression.
For example `+` accepts complex operands; `/` requires a nonzero divisor;
`sqrt` takes a nonnegative real argument. Resolved user declarations retain their
own source help. Builtins outside this catalogue keep available generic help;
the reader does not guess missing signatures.

The live reader supports draft editing and explicit checking; see Editing and
checking below. Rejected proof statements are marked red. The native preview
can also open `.lit` files and report failed verification or parse diagnostics,
including available source positions. A rejected fact
such as `1 = 2` and a parse error such as an undefined name remain distinct.
Static hosting opens previously exported reading JSON, without verification.

## Import source and save JSON

```sh
litex -reading -lang zh
```

This opens a browser backed by a service on `127.0.0.1`. Open/drop a `.lit`
file, or select/drop a complete project folder. A project must include its
`litex.config` files and dependencies. Several unrelated `.lit` files need
configuration to establish execution order. The viewer has no download button. Export JSON with the CLI below,
then reopen it to read without rechecking the source. A static export can also open existing reading JSON.

For reproducible builds or a website backend, invoke the exporter directly:

```sh
litex -reading -json -strict -lang zh -f chapter.lit > chapter.reading.json
litex -reading -json -strict -r book/ > book.reading.json
litex -reading -json -strict -e 'have x R
0 <= x ^ 2'
```

JSON mode starts no browser/server. It writes one `kind: "reading"` document
to stdout; exit 0 means the selected input verified, exit 1 can still contain
a useful partial bundle with `run_result: "failure"` and diagnostics. Check
both process status and document status. `-strict` rejects explicit user trust
and axioms. Without it, their origins and propagated dependencies remain
visible. Reading does not alter ordinary verification or Normal JSON output.

## Follow dependencies and inferred facts

Clicking a `prop` source statement shows its full predicate application and ⇔,
then an indented block containing every argument type and all complete defining
conditions in rendered LaTeX. The formula contains no prose or separate domain
heading. It presents the declared typed interface; the source domains and
quantifier scopes are preserved.
Click the source keyword `prop` to open the purpose/semantics guide and its
checked short example. Keyword help supports Enter/Space; Escape returns focus
to the source keyword. Selecting another statement restores mathematical content.

The selected source is not echoed; engine versions and source file/line
metadata stay out of the detail pane. Result/citation buttons select facts
separately. Concept highlighting follows resolved identity, including local
scopes. Mathematical metadata remains in the exported JSON independently of
which explanation the viewer chooses to show.

Optional `statement_kind` records the original tagged AST path, for example
`Definition.DefPropStmt`, `Definition.DefineObj.HaveObjInNonemptySetStmt`,
`By.ByDefStmt`, or `Fact`. It is available independently of execution status,
including unexecuted proof bodies and repeated execution contexts, and survives
static partitioning. The viewer does not guess the type from rendered source
or execution messages. Old bundles without it show neutral statement details.

Optional `declaration_symbol_ids` records direct named declarations from captured
typed fields. It excludes parameter and nested binders. The shared viewer places
a compact reference badge beside each mapped declaration; clicking it opens
current-file source snippets and clicking a snippet jumps to its exact token.
Counts use resolved identity and unique source spans, excluding declarations,
comments and generated inference output. Repeated execution and loading another
chapter do not inflate the current-file count. This reports source references,
not proof dependencies. Older bundles remain readable and use existing explicit
declaration metadata where available.

The source uses IDE-style colors for keywords, predicates, functions, objects,
types/sets, named theorems, numbers/constants, operators and punctuation.
Comments and inline asides are muted. Semantic colors use resolved identities,
declaration kinds and typed function-head evidence; a resolved identifier takes
precedence over the lexical catalogue. The catalogue is generated from current
parser spellings and tokenizer symbols with
`python3 src/reading/generate_highlighting.py`; use `--check` to detect drift.
Hovering or focusing supported tokens explains their language role; resolved builtin sets have brief
mathematical labels such as `R` → real numbers ℝ. Escape dismisses the tooltip.

The top-right **示例目录 / Examples** button opens chapter selection and search.
Resolved names show their recorded definition line and exact source declaration
on hover or keyboard focus; selecting a name also shows that declaration in the
inspector. Lazy chapters are loaded on demand. Missing source stays unavailable
rather than being reconstructed from a normalized statement. Compound keywords
such as `by def`, `by contra`, `have fn` and `release thm` share one help target;
clicking `by def` explains “用定义来证明”.

Mathematical output shortens a qualified name only when the recorded
configuration and symbol identity identify an unambiguous declaration in that
context. This applies to plain and retained LaTeX output; source spelling,
FactIds and citation targets remain unchanged. Unknown or ambiguous names
remain qualified.

An optional source `tokens` array carries normalized tokenizer `text` and original
UTF-8 `start_byte`/`end_byte` ranges. Comments and inline asides are excluded by
the language tokenizer. Unicode aliases keep their authored spelling in the
viewer. Resolved symbol occurrences take precedence over lexical highlighting,
so an identifier is never assigned a keyword meaning by spelling alone. Lazy
exports retain tokens in chapter chunks, not the initial index. Older bundles
retain ordinary source rendering and builtin-set help from resolved identities.

`examples/reading/inferred_facts.lit` contains this runnable sequence after
its definitions and object declaration:

```text
by def $reading_outer(reading_value)
$reading_inner(reading_value)
```

The producing line carries one compact grey **Inferred** button with a result
count; result text stays hidden until clicked. Its anchored popup lists the
actual published results, without inserting source text or extra source rows.
Click the button again, click outside, or press Escape to close it; Escape
returns focus to the button. Long results wrap inside the scrollable popup.
Each result retains its fact ID, including the ID cited by a later statement.
Clicking a result
or later citation shows the actual seed and inference basis, and selects the
producer in source. Buttons expose only inferred facts actually published
by that statement in its own execution scope. Parameter
assumptions and other temporary inferences used to check a `prop` definition
stay in the proof evidence; they do not become result buttons on the definition.
An executed nested proof statement can have its own local result button;
these remain local to that statement's scope.

Popup results omit origin prose. Selecting one shows the complete predicate
equivalence retained for its actual producer, highlighting the selected domain
or condition. Compact named definition links open the definition's mathematical
view. Failures, trust and local assumptions remain explicit. The default pane
does not show a rule catalogue or raw evidence tree; full typed evidence and
per-conclusion origins remain in JSON.

Optional `mathematics` data on statements is projected from the actual AST;
on inference batches it comes from retained parameter-type and complete
definition-expansion results. Parameter domains are outside the equivalence.
Set, nonempty-set, finite-set and element parameter kinds stay distinct.
Definition clauses preserve their full structure and order, including chains
and quantifiers. Published outputs may split a clause into several facts or
omit already-known facts, so they must never be used to reconstruct an iff.
Abstract predicates have no invented iff clauses. Display projection does not
instantiate through mutable Runtime methods or allocate proof identities.
Unsupported forms and older bundles show actual output facts where available,
or explain that mathematical display data is unavailable; the reader does not
guess from source strings. This is an additive schema-v2 display projection,
not a replacement for typed verification evidence.

Optional `mathematics.latex` has a `subject` formula and parallel `parameters`
and `facts` arrays for predicate definitions and complete retained predicate
expansions. Older bundles without `subject` use the retained readable subject. Each array
keeps the corresponding domain/clause order. The existing AST-to-LaTeX compiler
produces them without parsing display strings or executing statements. Ordinary
unguarded quantified comparisons use structural line breaks; guarded/nested
logic keeps the canonical grouped formula. Other long expressions can scroll
within the formula. Older data or unavailable conversion uses the complete
retained text. A missing/failed renderer also falls back to that text, with a
notice rather than raw LaTeX or a blank panel.

The export uses schema `"2"` and a shared evidence DAG. A reference such as
`{"kind":"evidence_reference","evidence_id":"evidence17"}` resolves through
`evidence_nodes: [{"id":"evidence17","node": ...}]`. Sharing removes repeated
copies; it does not discard child proofs. The viewer also reads schema `"1"`
inline evidence. Older bundles without inference records do not receive
guessed inline results.

`fact_reference` is an actual reference to a fact record. An AST fact's own
`fact_id` is exported as `fact_identity`: internal calculation subjects can
have an identity without being stored, published or cited. Do not turn these
subject identities into dependency links.

Useful records for a custom frontend:

| Record | Meaning |
| --- | --- |
| `sources` | Original source content, logical path and digest. |
| `statements` | Source/execution identity, optional `statement_kind` AST path and `mathematics` display data, scope, status, evidence, `produced_fact_ids`, `cited_fact_ids`, `inferred_fact_ids`, declaration/trust dependencies and coverage. |
| `facts` | Mathematical text, actual scope, producer and fact-specific evidence; `role` distinguishes hypotheses, verified facts and declarations. `inference_ids` links a derived fact to its recorded inference. |
| `inferences` | Actual store/infer output: seed, conclusions, producer, scope, batch `rule_ids`, retained evidence, optional `mathematics`, and `conclusion_origins` linking each stored conclusion to its own rule and available resolved definition. |
| `well_definedness` | Actual registered object, scope, creator statement, registration node and separately retained formation evidence when available. |
| `symbols`, `occurrences` | Semantic identities and exact half-open UTF-8 source ranges; comments are excluded. |
| `rules` | Kernel-derived catalogue, stable rule IDs and available authored labels. |

`produced_fact_ids` records publication in the statement's actual root scope;
`inferred_fact_ids` is the inferred subset of that statement's
`produced_fact_ids`. The full `inferences` index can also retain internal
verification inferences; do not render that whole index as statement outputs.
The viewer applies the publication boundary to older bundles as well.
`conclusion_origins` entries contain `fact_id`, `kind` (`definition`,
`parameter_type`, `rule` or `unavailable`), the actual `rule_id`, and available
`source_symbol_id` / `definition_statement_id`. They come from the nearest
typed infer branch around an actual stored conclusion, not the union of all
rules in the batch. A compound seed without an unambiguous named definition
does not receive a guessed definition link.
Use each fact's scope and producer, not a union of these lists as global
knowledge. A record's `coverage` describes exported information, separately
from whether verification succeeded. A rejected statement is not false.
`coverage.evidence` measures typed-payload projection. Statement
`coverage.well_definedness` checks whether its actual WD IDs have indexed
registrations and creator statements; missing IDs are listed explicitly.
A WD record's `coverage: "registration"` means that the memory registration
was retained, not that a separate recursive proof exists for every cached
lookup. The reader follows the actual registration/formation evidence and
labels missing information. Hypothesis formation evidence does not establish
the hypothesis as an unconditional fact.

All runtime-derived IDs are local to one bundle. `bundle_id` fingerprints the
complete snapshot; never reuse fact/statement IDs across different bundles.
Preserve `engine`,
`catalogue_id`, `input_digest`, `configurations` and `execution_policy` when
storing a bundle. Digests use deterministic non-cryptographic fingerprints;
they are not signatures or a way to authenticate an untrusted upload.
Catalogue identity alone is not a complete mathematical specification.

## Publish and embed

```sh
litex -reading -strict -lang zh -r book/ -export public/books/my-book
```

The directory contains `index.html`, complete portable `reading.json`,
`reading.manifest.json`, versioned `reading-data/` parts, `standalone.html`,
`reader.js`, `reader.css`, `app.js`, `katex.min.js`, `katex.min.css` and
`katex.LICENSE`. The math CSS embeds its WOFF2 fonts; no CDN is needed. Publish the whole directory with your
website. The normal page loads the entry chapter first, then each selected
chapter's source and proof DAG. The global search and concept occurrence
indexes load on demand. Search includes source comments/prose and paginates
results. Cross-chapter jumps use actual identity/dependency metadata.
No running Litex process
is needed for readers to follow already exported proofs.

`standalone.html` contains the complete data for opening the export from disk;
`index.html` redirects there under `file:` because browsers restrict fetching
local JSON parts. Both use the same viewer. See the
[three-chapter project](../examples/reading/book/README.md) for project order
and named cross-chapter interfaces.

The smallest integration is an iframe:

```html
<iframe src="/books/my-book/index.html" title="Interactive textbook"
        style="width:100%;height:85vh;border:0"></iframe>
```

For a component inside your own layout, load the exported styles and scripts
in this order, then open its manifest:

```html
<link rel="stylesheet" href="/books/my-book/katex.min.css">
<link rel="stylesheet" href="/books/my-book/reader.css">
<script defer src="/books/my-book/katex.min.js"></script>
<script defer src="/books/my-book/reader.js"></script>
```

```js
const reader = await LitexReading.open(
  document.getElementById('reader'),
  '/books/my-book/reading.manifest.json', {
  locale: 'zh',
  onNavigate(selection, { bundle_id }) { console.log(bundle_id, selection); }
});
// IDs come from this manifest/bundle; do not hard-code them across rebuilds.
await reader.selectStatement(selectedStatementId);
```

For an already loaded complete JSON, `LitexReading.mount(root, {
document: readingJson, locale: 'zh' })` remains available. `open` also accepts
an inline manifest plus `baseUrl` pointing to its URL. Parts must share that
origin and snapshot ID; failed loads report an error while retaining the
previous selection. “Open a file” is the primary action; the viewer has no
download control. The footer’s closed “Reading help” disclosure contains usage hints, the color
legend and an explanation of how statements
were checked, which facts were used and what was inferred. JSON remains the
transport format. Optional `onOpenFiles()` and `onOpenProject()` callbacks add
file/folder opening; the host owns file selection and validation. The supplied
shell opens saved records and, in live preview, Litex files and folders.
The example menu starts collapsed; there is no duplicate source selector.
Small file-local reference counts appear beside each explicit predicate, function
and object declaration; clicking a count opens its actual source uses. Definition
spans and inferred output do not count as references. Occurrence lists in the
detail pane still start closed.

Hover or focus a resolved name to see its exact authored declaration line and
source. Bound parameters also show their declared domain from typed parameter
evidence, independently of later inferred memberships: in `forall x Q:`, the
body’s `x` reports `x ∈ Q`, even when its statement checks `x $in R`. Same-name
binders are separated by symbol identity. When older records lack this evidence,
the reader keeps available source information without guessing a domain.

The returned component has `selectStatement(id)`, `selectFact(id)`,
`selectWellDefinedness(id)`, `getSelection()`, `getBundleId()`,
`setLanguage(locale)`, `update(nextBundle)` and `destroy()`.
Selection methods can return a promise while loading a chapter; await it
before depending on the new selection. `getSelection()` includes `source`,
`statement`, `symbol`, `fact`, `wd` and `focusLine`.
`update` resets navigation to the new document. `destroy` removes the mounted
view; call it when the host component unmounts. Styles are scoped to
`.lr-root`; standalone body styling requires `.litex-reading-page`.

An iframe announces `{type: 'litex-reading:ready', bundle_id, selection}`
after its reader and message handler are ready. Wait for that message, check
the snapshot ID against your metadata, then send selections:

```js
frame.contentWindow.postMessage({
  type: 'litex-reading:select', bundle_id: currentBundleId,
  fact_id: selectedFactId
}, new URL(frame.src, location.href).origin);
```

Use `statement_id` or `well_definedness_id` instead of `fact_id` for those
selections. The frame ignores selections with a different supplied bundle ID.
Older messages without `bundle_id` are still accepted for compatibility.
The frame
checks the sender's origin and `event.source === window.parent`, and reports
`{type: 'litex-reading:selection', bundle_id, selection}` back to the parent,
including after an uploaded bundle replaces the current document.
The parent must also check origin and `event.source === frame.contentWindow`.
The host's referrer policy must provide the referring origin for this bridge;
static reading itself works without the bridge. Hosting policies must allow
the chosen frame/parent. See the [runnable integration example](../examples/reading/website/README.md).

## Recheck edited source through an API

The local development server exposes the same exporter at
`POST /api/reading/build`:

```sh
litex -reading -no-browser -port 49181 -strict
```

```json
{
  "files": [{"path": "chapter.lit", "content": "have x R\n0 <= x ^ 2\n"}],
  "entry": {"kind": "file", "path": "chapter.lit"},
  "language": "zh",
  "strict": true
}
```

For a project, upload relative source/config paths together and use
`"entry": {"kind": "project", "path": "."}`. Entry can be omitted when one
root is unambiguous. The response is the reading bundle; HTTP 200 can still
have `run_result: "failure"`. Malformed upload requests return HTTP 400 and
`{"error": ...}`. The initial `GET /reading.json` remains the server's startup
document; the build response is the newly generated document.

The local server accepts builds from its own origin. A public webpage should
use its own backend to run `litex -reading -json` in an isolated request
workspace and return that JSON, then call `reader.update(result)`. It must
retain its own authentication, resource/concurrency limits and project
isolation; the development loopback service is not a deployed multi-user
execution service. Do not point a visitor's browser at your development
machine's `127.0.0.1` URL. Static embedding needs no execution endpoint.

Current upload limits are 512 source/config files, 8 MiB combined source,
16 MiB request body, and 300 seconds / 256 MiB output per child build. A server
started with `-strict` cannot be weakened by a request. Missing dependencies
and incomplete source are reported; they are not silently replaced.

The loopback service keeps up to 64 MiB of complete successful upload builds
in memory, with at most 32 MiB per request/result pair. Identical request
bytes, server strict policy and executable identity reuse the actual JSON;
changed source/configuration, entry, language or requested policy causes a
miss. `X-Litex-Reading-Cache` reports `hit`, `miss` or `bypass`. Requests with
external standard-library imports bypass caching because those files are not
part of the uploaded snapshot. Failed builds are not cached. Restarting the
service clears this cache. Command-line JSON/export builds still reverify;
this cache does not replace the ordinary knowledge-base cache or provide
incremental proof invalidation. Versioned static parts separately support
browser caching. Full portable JSON remains available for durable reuse.

### Human-readable example titles

A project may place `reading-titles.json` beside its independent `.lit` files:

```json
{
  "kind": "reading_titles",
  "sources": {
    "13-orthogonal-projection.lit": {
      "zh": "正交投影与唯一最近点",
      "en": "Orthogonal projection and the unique closest point"
    }
  }
}
```

The observer copies valid labels into optional `sources[].titles`. The shared
reader uses the selected language for page titles, example menus, source
menus, definition locations and search results. Both language labels can
be searched. Actual source paths, source bodies, digests and reference IDs
remain unchanged. Exported/lazy/offline reading data retain the titles; embedding
uses the same component. Older records without titles retain their source names.

Project uploads accept this specifically named sidecar alongside source/config
files. It does not count as an executable input. Missing, malformed, unrelated
or oversized title data fall back to source names and do not affect proof
checking. The sidecar is limited to 64 KiB; individual nonempty locale labels
are limited to 300 characters. This is presentation metadata, independent of
mathematical verification and the source input digest; bundle fingerprints
include it. The main mathematical example collection supplies both Chinese and
English titles for every source.

## Independent problem examples in the homepage gallery

`python3 examples/reading/homepage/export_gallery.py <output-directory>` builds
the usual strict collection plus four independent problem/correction pairs.
The Examples menu groups entries as Passes / Does not pass, including normal
chapters and the independent pairs. Case pages retain both categories and a
link to the remaining passing collection. Expected failures retain their actual
failure status. `--reuse-main` reuses a previously verified main export without rerunning
its mathematics. The supplied builder validates all eight exercise outcomes.

Hosts may pass optional `exampleGroups` to the shared reader: each group has
`titles: {zh, en}` and `items: [{titles: {zh, en}, href: "cases/example/"}]`.
A group may set `includeSources: true` to include this bundle’s source chapters
in that category instead of listing them again outside the categories.
Only relative directory links with optional parent segments are accepted. The
supplied shell reads host-authored groups from an optional JSON script with
id `reading-example-groups`; this is host navigation metadata, separate from
proof JSON. Cross-page links retain the current locale using `?lang=zh|en`.
The gallery versions its shared asset URLs to prevent cached old scripts from
hiding freshly added navigation. Existing exports without groups still work.


## Editing and checking

When a checking host is available, every example opens directly in one IDE
surface: editable source, semantic colors, line numbers and quiet grey inference
buttons. Checked tokens retain their resolved hover cards; Ctrl/Cmd+click opens
their existing definition/language help, and popup results remain clickable.
There is no Edit/Read mode switch. Tab insertion and indented newlines are supported.
Use **Check** or Cmd/Ctrl+Enter to submit it. Any input immediately invalidates
the old verification badge, inferred results and mathematical detail. A response
is applied only if the submitted draft revision and document are still current.
Checks execute the selected file with its real ordered project prefix. Later
chapters retain only editable source and say Chapter not checked; they never
reuse old proof evidence. Failed checks keep the draft and show the verifier's
actual diagnostics. **Restore original** restores this page's initial text; run Check again to verify it.
Drafts stay in this page's memory and do not write to the original file.

The shared component accepts optional `onCheck({changes,sourcePath,locale})`,
which returns a complete fresh reading document. `getProjectSnapshot()` loads
the source contents and recorded configurations when a host needs them. The
supplied shell reconstructs closed, single-configuration projects in original
export order and preserves strict checking. Nested/external module dependencies
are explicitly rejected by this initial editor bridge. After an input, old inferred facts and semantic hover are cleared immediately;
the draft uses lexical colors until checking returns fresh evidence. Source
selection opens or updates the contextual explanation without replacing the input or losing
the caret. Editor scroll and selection are retained through navigation/checks.

Static exports stay read-only unless their host supplies a checking endpoint.
For the local gallery, run the native reader and same-origin proxy separately:

```sh
target/release/litex -reading -strict -no-browser -port 49186
python3 examples/reading/serve_gallery.py /path/to/exported-gallery --port 49187
```

The proxy injects an opt-in endpoint into served HTML and forwards builds to
the existing native loopback service; it does not execute proofs itself or
modify exported source. This is a local development server. Check output is
bounded to 256 MiB, with a 300-second child-build timeout for large chapter
prefixes. Source/request/concurrency policies are otherwise
unchanged. Published websites still provide their own checking service.

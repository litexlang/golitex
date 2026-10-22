# Interactive Litex reading

Reading exports the verification evidence of a Litex file or project. The
same JavaScript reader uses that JSON in a local browser or a hosted webpage.
Its source pane and explanation pane share statement IDs, fact IDs, semantic
symbol identities and actual verifier citations.

## Import source and save JSON

```sh
litex -reading -lang zh
```

This opens a browser backed by a service on `127.0.0.1`. Open/drop a `.lit`
file, or select/drop a complete project folder. A project must include its
`litex.config` files and dependencies. Several unrelated `.lit` files need
configuration to establish execution order. Choose “下载 JSON” to save the
currently displayed bundle. Reopen that JSON to read it without rechecking
the source. A static export can also open existing reading JSON.

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

Click a source statement to see its actual cited facts, rule applications,
and definition/theorem uses. Click a cited fact to visit its producer. Concept
highlighting is separate and follows resolved identity, including local scopes.

`examples/reading/inferred_facts.lit` contains this runnable sequence after
its definitions and object declaration:

```text
by def $reading_outer(reading_value)  → reading_value $in R · $reading_inner(reading_value)
$reading_inner(reading_value)
```

The arrow and following results are compact grey annotations on the producing
statement's source line, not inserted Litex source or extra display rows.
Long lines scroll horizontally within the source pane. Each result retains
its fact ID, including the ID cited by a later statement. Clicking a result
or later citation shows the actual seed and inference basis, and selects the
producer in source. Annotations show only inferred facts actually published
by that statement in its own execution scope. Parameter
assumptions and other temporary inferences used to check a `prop` definition
stay in the proof evidence; they do not become annotations on the definition.
An executed nested proof statement can have its own local output annotations;
these remain local to that statement's scope.

Inline results omit origin prose. Citation and inferred-fact detail cards
retain each conclusion's origin. For example, the argument-membership
fact is labelled “由 reading_outer 的参数类型推出”, while the inferred
`$reading_inner(reading_value)` is labelled “由定义 reading_outer 展开”. Click
the origin label to visit that exact declaration; other named rule labels open
their Rule Book entry. The same origin appears on citation and inferred-fact
cards. Missing per-conclusion provenance in an older bundle is labelled as
unavailable, not guessed from the enclosing statement's rule list.

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
| `statements` | Source/execution identity, scope, status, evidence, `produced_fact_ids`, `cited_fact_ids`, `inferred_fact_ids`, declaration/trust dependencies and coverage. |
| `facts` | Mathematical text, actual scope, producer and fact-specific evidence; `role` distinguishes hypotheses, verified facts and declarations. `inference_ids` links a derived fact to its recorded inference. |
| `inferences` | Actual store/infer output: seed, conclusions, producer, scope, batch `rule_ids`, retained evidence, and `conclusion_origins` linking each stored conclusion to its own rule and available resolved definition. |
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
`reader.js`, `reader.css` and `app.js`. Publish the whole directory with your
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

For a component inside your own layout, load `reader.css` and `reader.js` from
that export, then open its manifest:

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
previous selection. The download button always saves the complete snapshot,
including chapters that have not yet been visited.

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
document; the build response/download is the newly generated document.

The local server accepts builds from its own origin. A public webpage should
use its own backend to run `litex -reading -json` in an isolated request
workspace and return that JSON, then call `reader.update(result)`. It must
retain its own authentication, resource/concurrency limits and project
isolation; the development loopback service is not a deployed multi-user
execution service. Do not point a visitor's browser at your development
machine's `127.0.0.1` URL. Static embedding needs no execution endpoint.

Current upload limits are 512 source/config files, 8 MiB combined source,
16 MiB request body, and 120 seconds / 128 MiB output per child build. A server
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

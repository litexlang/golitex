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

Preview opens a browser; `-no-browser` prints the URL without opening one.
Use `-port 49181` to choose a port, `-lang zh` for Chinese presentation and
`-strict` to use the verifier's strict execution policy. File/project inputs
use the existing project loader. `-e` uses isolated source evaluation.
Bare preview accepts `.lit` files, a complete project folder, or an existing
reading JSON bundle. A dependent source needs its project configuration and
dependencies. The local service listens only on `127.0.0.1`.

The viewer follows the typography and palette of `../litex-webpage`: a light
background, green controls, blue current statements, green cited facts and
purple concepts. The initial selection prefers an accepted statement with
actual citations. Premises lead into a conclusion card. Statement and fact
details show concise origins, citations and rules, without full proof-tree
expanders or related-concept lists. Source concepts remain clickable, and
complete execution evidence remains in the exported JSON. The Rule Book
starts collapsed. The same viewer handles local preview and static export
without a Node runtime or frontend build.

Source ranges use original UTF-8 byte offsets. Occurrence highlighting uses
resolved identities and reports mapping coverage per statement. Typed proof
payloads and retained local scopes are exported. Actual store/infer outputs
link seed facts to derived fact IDs; the reader displays compact grey results
beside the producing statement on the same source line, excluding temporary
definition/parameter-checking assumptions, and can follow a later citation
back to an inferred fact. These inline results omit origin prose and do not
add display rows; long source lines scroll horizontally within the source pane.
Citation and inferred-fact detail cards name each conclusion's retained origin,
distinguishing definition expansion from parameter typing. Available named
definition labels link to the actual declaration; other rule labels link to
the Rule Book. Older bundles without this metadata report the gap.
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

Or load `reader.css` and `reader.js`, then mount the viewer into an existing
element. Its styles are scoped to the reader; standalone page styles require
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

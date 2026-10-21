# Interactive reading design

Status: target design with an initial implementation. The [README](README.md)
lists currently implemented commands, embedding and limitations. The sections
below retain the full target and illustrative record shapes; they are not a
claim that all acceptance criteria have passed or a frozen public API.

## Goal and evidence

Accept a standalone Litex file or complete project and produce a browsable
record of its source, concepts, facts and actual verification grounds.
The same reader should work in a local browser and inside a published website.
Source authors should not need to annotate every proof dependency by hand.

The existing result tree already retains useful evidence. For example,
[the nonnegative even-power rule](../execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_rules/less_equal.rs)
has this success payload:

```rust
pub struct EvenPowNonnegativeBuiltinRuleProof {
    pub base_in_real_proof: VerifyFactResult,
}
```

[Detailed projection](../json_output/project_detailed/builtin_atomic_gen.rs)
exports that child proof. This establishes a starting point for evidence
projection, not complete coverage of every reading interaction. The existing
[even-power fixture](../../examples/proof_nodes/atomic/by_builtin_rule/less_equal_even_pow_nonnegative.lit)
is the first source anchor for implementation; it has not been rerun as part
of creating this directory.

Exact occurrence mapping is a separate unfinished boundary.
[TokenBlock](../tokenize/token_block.rs) retains original source and token
byte ranges, while [SourceLine](../ast/line_file.rs) carries source identity
and a line. The tokenizer ranges are not yet a complete token-to-resolved-
symbol map. [IdentifierObj](../ast/obj.rs) distinguishes local IDs and
qualified module/export names; displayed spelling alone is insufficient.

## Responsibilities and dependency direction

```text
source / project configuration
  -> existing project loading, parsing and statement execution
  -> typed Exec / Verify / Store / Infer evidence and retained scopes
  -> reading projection + source/identity mapping + rule metadata
  -> versioned reading bundle
       -> shared viewer in the local preview
       -> shared viewer in a published website
```

| Responsibility | Owner | Contract |
| --- | --- | --- |
| Project loading | Existing launch/run and module layers | Preserve configuration, imports, export order and registered-file prefixes. |
| Mathematical verification | Existing execution/verifier/storage layers | Evidence remains authoritative; reading does not add facts or search for a different proof. |
| Reading model and export | This module | Resolve exported references from real evidence, retain scope and distinguish missing coverage. |
| Source and concept mapping | This module, using existing parser/tokenizer information | Associate exact original-source occurrences with resolved identities. |
| Rule catalogue | Kernel-owned metadata exposed through this module | Maintain one rule identity and description source alongside each rule family. |
| Browser viewer and assets | This module | Render generic concepts, statements, evidence applications and links. |
| Preview and static publishing | This module, invoked by launch/run | Local and hosted presentation use the same bundle and viewer. |
| Book-specific content | Book/showcase owners | Supply chapter order, prose and optional figure configuration. |

Add implementation files only as these responsibilities are implemented.
Keep `mod.rs` for declarations and exports. Do not precreate empty branch
modules or a second family of verification result types.

## Proposed command surfaces

These commands are implemented by the initial reading branch. The current
binary name is `litex`.

```sh
litex -reading
litex -reading -f chapter.lit
litex -reading -r book/
litex -reading -json -r book/ > book.reading.json
litex -reading -export ./book-site -r book/
```

- Bare reading mode starts a loopback service, opens the browser, and accepts
  selected or dropped sources. The service invokes the same reading exporter
  as batch mode. Missing browser launch support should leave a usable local URL.
- File and repository modes initially load their selected content using the
  existing project semantics. A dependent uploaded file requires its project
  context; missing dependencies must be reported rather than silently omitted.
- JSON mode writes one machine document without starting a browser or service.
- Static export writes the viewer assets and reading data for publication.
  Build-time frontend tooling must not become a requirement for opening an
  installed local reader or browsing a published book.

Represent mutually exclusive actions as launch enum variants, following the
existing command structure. Keep the ordinary verifier commands and existing
JSON contracts intact. HTTP dependencies, asset packaging and platform browser
launch support remain implementation decisions; Cargo currently declares no
dependencies, so additions require an explicit dependency/packaging assessment.

## Proposed reading bundle

The exporter consumes typed results directly. It must run while the required
runtime/module metadata and retained local evidence are still available.
The [runner result](../run/run_command_outcome.rs) already attaches Normal
JSON before its runtime disappears; a late serializer cannot assume every
cited local fact remains on the final live stack. Traverse the evidence's
actual retained scopes and producers without publishing local facts globally.

| Records | Required meaning |
| --- | --- |
| Manifest | Schema version, engine build identity, input/dependency digests and rule catalogue identity. |
| Sources | Original text, logical project paths, content digests and source ranges. |
| Symbols and occurrences | Definitions, semantic identities and exact reference ranges, including module ownership. |
| Statements and scopes | Source ordering, nested proof boundaries, local parameters and assumptions. |
| Facts and evidence steps | Actual produced facts, citations, selected proof routes, definition/theorem applications and inferred consequences. |
| Rules | Stable machine identity, family, localized presentation and available mathematical description. |
| Diagnostics and coverage | Rejected statements, hard termination, explicit trust/axiom origins and missing export coverage. |

For example, a rule application might have this shape. References point to
other records omitted from this illustrative fragment; these are not current
Litex output fields:

```json
{
  "id": "step8",
  "kind": "rule_application",
  "rule_id": "builtin.less_equal.even_pow_nonnegative",
  "premises": [
    { "role": "base_in_real", "proof_id": "proof4" }
  ],
  "conclusion_fact_id": "fact8",
  "scope_id": "scope0",
  "source_statement_id": "statement2"
}
```

Machine keys and identities must be independent of display language.
Namespace runtime-derived IDs within their build; they are not permanent
cross-build links. Preserve qualified owner identity instead of persisting
unqualified names or raw module indices as universal identities.

Keep symbol occurrence edges separate from mathematical dependency edges.
Also distinguish truth premises, well-definedness obligations, definition
expansion, theorem application and inference. A repeated word is not a proof
citation. A recorded winning route is not an inventory of all possible proofs.

Byte ranges refer to the exact source digest and use half-open UTF-8 offsets.
Convert them explicitly for browser APIs that use UTF-16 positions. Preserve
comments, aliases and multiline input positions. Generated facts without a
literal source span should link to their producer, without invented ranges.
Prototype token-to-identity capture before claiming full concept highlighting.

Report coverage per relevant record. An accepted statement with partial export
must remain distinguishable from one whose whole evidence was exported.
A rejected statement is not a proof of its negation. Partial failed-run
bundles may expose the accepted prefix, but must not label the entire input
verified. Trust and axiom boundaries remain visible through dependencies.

## Rule catalogue evolution

Give each exported rule an identity independent of localized labels and
incidental Rust renaming. Keep actual rule application evidence separate from
catalogue metadata. A builtin search leaf, an inference rule and an explicitly
invoked builtin theorem have distinct roles even if one browser presents them
in a common searchable book.

Adding an exportable rule should include its catalogue identity/metadata,
typed application projection and coverage checks. Check that application rule
IDs resolve to the bundled catalogue. Organize metadata so catalogue export
does not require constructing fake proof instances, and do not maintain a
second hand-copied rule list in the website. Mathematical descriptions require
authorship; arbitrary Rust code cannot supply a complete rule specification.

Preserve the engine and catalogue identity in every published bundle. Rebuild
content against a newer kernel deliberately; old content keeps its original
catalogue. New rules using supported record shapes should render through the
generic viewer. Schema changes and genuinely new interaction kinds may require
a viewer upgrade.

## Website integration

Static browsing needs the generated data and JavaScript viewer, without a live
Litex process. Deploy the static export and embed its published URL in an
iframe, or mount the same viewer directly inside the existing website.
An iframe is the smallest integration; direct mounting allows closer styling
and navigation integration. A local loopback URL is a preview on that machine,
not a public hosting endpoint.

```html
<iframe
  src="/books/mechanics/index.html"
  title="Interactive Mechanics textbook"
  style="width:100%; height:85vh; border:0"
></iframe>
```

The deployed page's embedding policy must allow its parent. Parent/viewer
coordination can use origin-checked messages; see
[frame-ancestors](https://developer.mozilla.org/en-US/docs/Web/HTTP/Reference/Headers/Content-Security-Policy/frame-ancestors)
and [postMessage](https://developer.mozilla.org/en-US/docs/Web/API/Window/postMessage).

Editing source and rechecking it is a separate execution capability. A future
website endpoint such as `POST /api/reading/build` would invoke the same
exporter and return the same bundle, with isolated users and bounded execution.
It is not required for clicking through prebuilt evidence. The current text
REPL is not a machine HTTP protocol. Any later incremental editor must preserve
accepted context and explicitly invalidate/replay it when earlier source changes.

## Implementation sequence and acceptance

1. Export one real evidence path and show it in a minimal viewer. Start with
   the even-power fixture above, then connect an actual later fact that uses
   earlier evidence. Assert source and citation correspondence rather than
   inferring it from display strings. Mark incomplete coverage explicitly.
2. Add precise occurrence mapping and Rule Book linkage. Exercise sibling-scope
   name reuse, qualified same-name exports, nested proofs, UTF-8 positions,
   comments and multiline input. Keep unsupported mapping visible.
3. Connect local browser preview, JSON mode and static export to the same
   pipeline. Load the same source through each and compare the semantic records.
   Check failed input, missing dependencies and partial output.
4. Use unchanged viewer code for small Mechanics, linear algebra and geometry
   excerpts, then add chapter navigation and chunked loading for a whole book.
   Graphical figures need optional explicit scene data; ordinary proof export
   does not automatically recover a geometric drawing.
5. Add live website verification when requested, with the same export contract.

The first end-to-end acceptance must demonstrate statement selection, actual
premise tracing, rule navigation and concept highlighting entirely from the
exported data. Boundary acceptance must prevent cross-scope fact leakage,
same-spelling symbol conflation and false complete-verification labels.
Introducing another ordinary book should require content/configuration rather
than book-specific mathematical interpretation in the viewer.

## Change boundaries

Implement the additive reading branch under the existing execution pipeline;
classify producer/consumer contract checks when executable work starts.
New public output is normally an L3 contract surface; source capture or state
changes require their own impact assessment. Register a durable runnable tracer
when the first user-visible capability is implemented.

Use unchanged existing AST, Env, Runtime and module interfaces wherever they
provide the required evidence. This design does not authorize protected struct,
ID-allocation, scope-lifetime, storage or transaction changes. If precise source
capture or scoped citation export needs such a change, present the concrete
proposal before editing those owners. An export-local map must not become a
parallel semantic store that bypasses that boundary.

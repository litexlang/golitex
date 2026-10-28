# Shared reader component acceptance

These tests run the unmodified public `LitexReading.mount` API and its actual
DOM event handlers using real CLI-generated reading bundles. They need Node.js
and Python, with no npm package installation or browser access.

```sh
python3 src/reading/web/tests/fixtures.py tmp/reading-web-tests
node src/reading/web/tests/run.cjs tmp/reading-web-tests
node src/reading/web/tests/app.cjs tmp/reading-web-tests
```

Choose a task-owned output path for development evidence. `fixtures.py` requires
the release executable by default; pass `--binary` to select another build.
Passing sources must exit zero and failures must exit one, with a matching
reading `run_result` and exact retained source snapshot.

The sqrt-two equality-chain acceptance hovers each of the three equals signs
on source line 7, checks its exact adjacent relation and its own citations,
and follows a citation before returning to that precise step. Keyboard
selection, whole-line reset and edit invalidation use the same public events.
Degraded exported-record controls remove one proof or endpoint, remove an
operator token, or introduce ambiguous primary ownership; the renderer must
not borrow another step's proof when the mapping cannot be established.

`app.cjs` runs the unmodified page shell together with the real shared reader.
It checks localized and legacy menu links, alternate-page navigation, preserved
edits/opened documents, excluded cross-origin links, actual source checking
payloads, prefix-only projects, missing predecessors and complete-book metadata.
All fetches and locations in this suite are deterministic in-memory fixtures;
it performs no browser or network access.

For the complete edit/check path, export `examples/reading/book`, then run:

```sh
node src/reading/web/tests/host.cjs <book-export> target/release/litex <task-owned-output>
```

The unmodified shell/reader read actual source/proof parts. Each build request
writes its exact submitted files into that output directory and invokes the
real strict release CLI, rather than returning a canned verdict. It checks a
failed definition instance, a blocked later chapter, restore and keyboard
checking, new inference data, line-number tap/Escape, and preserved navigation
during a failed response. It also exercises the iframe ready/selection protocol,
actual changed-bundle guards, opaque referrers, cleared draft selections and
disposed-reader behavior. Transport is file-backed/in-memory; no browser or
network access is involved. Browser geometry and touch hit areas remain outside
this suite.
If the verifier independently accepts the next statement in a failed file, its
current proof must remain visible. Only genuinely unexecuted later chapters
remain source-only; an overall failure is not a per-statement failure verdict.

For the annotated lessons and their concrete repairs, generate actual CLI
fixtures with `fixtures.py <task-owned-output> --lessons`, then run
`node src/reading/web/tests/lessons.cjs <task-owned-output>`. This checks all
18 source views and uses six successful real repaired bundles after submitting
the exact edited bytes. Each lesson exercises its intended reading move.

Run `node src/reading/web/tests/predicate-proof.cjs <fixture-directory>` with
those same fixtures for combined predicate definition/proof hover. It covers
the actual intersection strategy and direct builtin-rule paths, each retained
member-set proof, a `by def` instance, local abstract-predicate assumptions,
the negative intersection goal and its contradiction closing proofs. The
literal `1 $in intersect({1, 2}, {2, 3})` is a real rejected CLI case and must
show failure rather than a success proof. A degraded requirement/proof pairing
must fail closed, and full bundles remain unchanged after display.

`gallery.py <exported-gallery>` validates every authored menu target, localized
lesson snapshot, alternate-page link, and shared asset/version hash. Run
`node src/reading/web/tests/static.cjs <fresh-native-export>` for the exported
offline bootstrap's language/URL-fragment preservation. These remain static and
component checks, separate from real browser acceptance.

Export the real `examples/reading/book` project, then run
`node src/reading/web/tests/lazy.cjs <export-directory>`. The public `open` and
snapshot APIs use actual exported files through a closed file-backed fetch
fixture. Assertions cover lightweight source requests, concurrent/cache
behavior, subsequent proof navigation, older exports, mismatched identity/path,
missing text, network retry, cross-origin parts, and document-change/destroy
cancellation. No browser or network request is made.

The same suite checks working-copy search against both lazy and complete
documents: replaced text disappears, inserted lines have their current numbers,
draft hits carry no old statement identity, restoration refreshes results, and
a delayed retained search index cannot overwrite an intervening edit.

`node src/reading/web/tests/anchoring.cjs <fixture-directory>` supplies explicit
DOM rectangles to the actual shared reader. It checks exact pinned-equality
positioning and dismissal of explanations, keyword help, proofs and inference
cards at the editor's vertical/horizontal clipping boundaries. This verifies
the positioning decisions, not actual browser geometry, CSS or touch behavior.

For a large existing book export, `lazy.cjs <export-directory> --measure`
checks every source against its retained content fingerprint, records actual
source payload bytes versus the previously required proof chunk sizes, and
opens its longest source chapter with its real proof part. Timing is an offline
component measurement, not a browser or network benchmark. Content fingerprints
are reproducibility checks, not cryptographic signatures.

`dom.cjs` is a deterministic event/DOM fixture, not a browser or CSS layout
engine. The suite proves record-to-interaction behavior and state transitions;
it does not prove typography, pointer hit areas, responsive layout or complete
accessibility. Actual browser/visual acceptance remains separate. No tests
rewrite reader source or export private implementation hooks.

The native checking transport has separate Rust acceptance:
`cargo test --release --lib reading::compact_json_output::tests` checks streaming
format fidelity, including Unicode, escapes and buffer boundaries;
`cargo test --release --test reading_http --test reading_site` exercises the
actual loopback service, child verifier, cache, failures, policies and exports.
The upload response is compact JSON with complete values; the ordinary CLI
continues to emit formatted JSON.

# Shared reader component acceptance

These tests run the unmodified public `LitexReading.mount` API and its actual
DOM event handlers using real CLI-generated reading bundles. They need Node.js
and Python, with no npm package installation or browser access.

Generate `--failed-case-context` fixtures and run
`node src/reading/web/tests/failed-case-context.cjs <fixture-directory>` for
actual failed-case assumptions, completed body prefixes, exact failing steps,
unexecuted suffixes, nested conditions and closing-goal/contradiction failures.
The canonical source is
`examples/test_statements/negative/by_cases_stmt/failed-body-context.lit`.
Bilingual editable/read-only events check source-row stability, condition
citations, navigation/back, keyboard focus and edit invalidation. Missing,
foreign or conflicting source/stage/scope records cannot create hypotheses.
Native retention and recovery are checked by
`cargo test --release --test reading_case_contexts`. These checks cover selected
case/body paths; they do not certify every statement failure or browser layout.

Generate `--completed-case-prefix` fixtures and run
`node src/reading/web/tests/completed-case-prefix.cjs <fixture-directory>` to
check coverage and completed cases before a later failure, including a completed
contradiction case, nested/quantified bodies, several completed cases and a
partially completed list of closing targets. The canonical negative tracer is
`examples/test_statements/negative/by_cases_stmt/completed-branch-before-failure.lit`.
Public events check exact local assumptions and citations, navigation/back,
folded body inferences, conditional target identities, unexecuted suffixes and
source invalidation in both languages and editor modes. Removed or reordered
coverage/branch/scope/closing records cannot certify earlier cases. The existing
`reading_case_contexts` Rust tests also check that a sibling's predicate and
inferred inequality are not published or usable outside their case.

Generate `--completed-case-prefix --case-consequences` fixtures and run
`node src/reading/web/tests/case-consequences.cjs <fixture-directory>` for
case-header consequences and per-conclusion rule explanations. Existing
unfinished cases and two strict successful controls exercise separate
`ParamTypes`/`ExpandDefinition` effects, reused target identities, outer
publication, local context and source/definition navigation. Bilingual
editable/read-only events check initially closed disclosures, actual rule
names, return navigation, edit invalidation and unchanged native records.
Missing or conflicting origins, native store effects, producers and sources
cannot supply another conclusion's rule or definition. These are file-backed
public event checks, not browser geometry tests.

Generate `--logic` fixtures and run
`node src/reading/web/tests/logical-actions.cjs <fixture-directory>` for native
contradiction assumptions, same-row block conclusions, case coverage and exact
branch scopes, claim/universal contexts and temporary inference outputs. The
sqrt-two tracer keeps the proved target at the block header and the actual
reverse assumption at `?`; Cantor supplies genuine local inferred facts. Native
positive and negative goals, compound existential/universal contradictions,
failed coverage/conclusions, malformed identities/scopes/anchors, pinning,
source edits and both pointer/keyboard paths are exercised bilingually. The
induction fixture checks the existing repeated-execution chooser and a reused
native FactId without inventing a new producer. It does not establish complete
induction annotations. Source/proof/scope records must remain unchanged.
These tests model neither browser geometry nor every statement form.

Generate `--empty-domains` fixtures and run
`node src/reading/web/tests/empty-domains.cjs <directory> [export]` for the
actual empty-parameter-domain universal proof. Existing public sources cover
proved carrier emptiness, a literal empty carrier, additional set-kind
parameters and a later empty group after a real parameter. The empty-carrier store remains private; the quantified false
consequent is not published separately, and an undefined consequent still
fails. Index/carrier/equality/store/scope/name and missing WD controls preserve
honest partial-data behavior. The optional two-source native export checks
lazy vacuous proofs with separate module scopes. Formation checks
remain last and closed for both vacuous and known universal certificates.

Generate `--processes` fixtures and run
`node src/reading/web/tests/proof-processes.cjs <fixture-directory>` for native
ordinary/strong induction, finite enumeration, `by for` and all three witness
forms. Current exports retain exact structured induction title anchors. Public
hover/focus, pinning, repeated phase selection, actual case goals and scope
identities, universal strong hypotheses, proved/skipped/empty enumeration,
witness bindings and uniqueness, final closed WD and edit invalidation are
checked in both languages. Rejected mathematical inputs and removed/conflicting
positions, scopes, conditions and obligations must not create guessed proofs.
Native source-position acceptance is
`cargo test --release --test reading_block_anchors`. These tests preserve the
input bundle and model no browser geometry.

Generate `--introductions` fixtures and run
`node src/reading/web/tests/object-introductions.cjs <fixture-directory> [namespaced-export]` for
the eight native object-introduction forms. Actual CLI inputs cover multiple
and dependent carriers, set kinds, ordinary/unique/multiple witnesses,
predicate argument versus existential-name correspondence, returned and field
function preimages, local and repeated executions, and replacement images.
Public pointer/focus/pin/citation/edit events verify exact property IDs, final
closed WD, source/body inference anchors and adjacent-row context continuity.
Controls remove or conflict with source declarations, stores, proofs, names
and selected interfaces. Parse rejections are reported separately from actual
mathematical rejections. No input records are modified and no browser geometry
is modelled. The optional native three-source export checks lazy loading,
resolved cross-file identities and source navigation without exposing internal
module prefixes as public names.

Generate `--functions` fixtures and run
`node src/reading/web/tests/function-definitions.cjs <fixture-directory> [namespaced-export]`
for the six native function/algorithm definition forms. Real sources cover
formula return bounds, guards, higher-order inputs and returns, empty complete
domains, unique existence, local name reuse, nested recursion, coverage and
pairwise disjointness. Bilingual pointer/focus/pin/citation/edit events preserve
native property IDs, source branches, local scopes, closed final WD and source
row count. Missing or conflicting proof, pair, store, source and identity
records cannot create guessed obligations. Actual parse rejection is distinct
from verifier failure. The optional six-source export checks lazy chunks and
resolved public names while retaining the independently observed namespace-eval
failure; an accepted definition must not turn that overall run into a success.
No input evidence is modified and no browser geometry is modelled.

Generate `--expansions` fixtures and run
`node src/reading/web/tests/expansion-proofs.cjs <fixture-directory> [namespaced-export]`
for seven native extensionality, explicit definition-release and range-expansion
forms. Fourteen exact public successes and seventeen real rejections exercise
both subset directions, complete function domains, curried applications,
known-universal reuse, object/struct sources, Cartesian definitions, tuple
shape/domain/coordinate checks and range alternatives. Actual parser failures
are distinct from mathematical rejections. Bilingual editable/read-only events
check hover/focus, pinning, citations and return, publication-root inference
ownership, final closed WD and invalidation after an edit. Missing and
conflicting records must remain incomplete. Optional seven-source native
exports exercise lazy chunks and resolved names through the public open API.
These strict fixtures do not establish non-strict trust-origin coverage or
browser geometry; source and native proof records remain unchanged.

Generate `--state-changes` fixtures and run
`node src/reading/web/tests/context-changes.cjs <fixture-directory> [namespaced-export]`
for seven registration, explicit-assumption and scratch-block forms. Exact
public sources cover all three checked properties, trust, trust-introduced
objects, named axioms and discarded scratch scopes. Non-strict trust/axiom
fixtures are deliberate assumption-origin tests. A same-context Session checked
the additional `release obj def trusted_a` boundary; it retains the original
trust provenance without claiming a proof. Strict-mode rejection, invalid
formation, false laws, malformed syntax and escaped scratch names retain their
native verdicts. Bilingual editable/read-only events check hover/focus, pinning,
definition/property navigation, native truth-versus-assumption distinction,
final closed WD, missing/conflicting records and edit invalidation. Optional
seven-source native exports exercise lazy chunks and resolved cross-file names.
These tests preserve source/proof/scope/producer identities and model no browser
geometry.

Generate `--interfaces` fixtures and run
`node src/reading/web/tests/interfaces.cjs <fixture-directory> [namespaced-export] [--require-field-anchors]`
for predicate/abstract-predicate, theorem/strategy and struct/template
definitions. Real sources exercise native definition clauses, untyped abstract
arguments, proved goals, strategy registration without universal stores,
ordered fields, structural existential laws and template body executions under
their original source owner. The full dispatcher template example is explicitly
non-strict because its final case is `trust have`; that origin remains visible.
Actual parse/verification failures and removed/conflicting scope, condition,
proof, publication and source records must not fabricate explanations.

Bilingual editable/read-only events check definition-versus-proof roles, body
ownership, source navigation, final closed WD and edit invalidation. Current
native producer acceptance is `cargo test --release --test reading_block_anchors`;
the optional field flag requires accurate native field positions. Consumer
controls remove or corrupt binding/index/range/multiplicity, and old exports
retain header field information without guessing positions. Optional six-source
native exports exercise lazy chunks and resolved cross-file names. Source,
proof, scope and producer identities remain unchanged by display; browser
geometry is outside these tests.

For object symbol explanations, reuse the `--struct-introduction-history` and
`--automatic-struct-origins` fixtures and run
`node src/reading/web/tests/object-symbols.cjs <fixtures> [export-or-compiler-json] [plain-introduction-fixtures]`.
The optional plain fixtures come from `--introductions`. Bilingual editable and
read-only events check actual declaration ownership, given values versus
choices, explicit trust, structural parameters and failed-check temporaries,
one domain, closed and citable properties, exact reference/Back navigation and
edit invalidation. Missing, foreign and ambiguous identities cannot borrow an
introduction; legacy mathematical models retain a neutral domain summary.
Real paths and authored titles remain visible while native virtual Eval paths
receive a readable label. Optional multi-source exports exercise lazy loading.
These checks preserve native records and do not observe browser geometry.

Generate `--template-contexts` fixtures and run
`node src/reading/web/tests/template-contexts.cjs <fixtures> [<fixtures>/template-context-book]`.
The actual sources cover set-kind and dependent parameters, predicate guards,
their inferred domain/definition conditions, structural parameters, object and
function bodies, incompatible guards, rejected instances, failed premise
prefixes and body formation failures. Bilingual editable/read-only events check
conditional publication versus local assumptions, actual inference rules and
source links, closed same-row consequences, exact reference/Back navigation,
stable symbol help and edit invalidation. Missing/foreign parameter, guard,
formation, scope, store and inference records cannot supply another context.
The optional two-source export or compiler JSON checks qualified definition
loading and exact return. Source and Native records remain unchanged; browser
geometry and all internal template failure branches are outside this gate.

Generate `--glossary` fixtures and run
`node src/reading/web/tests/language-reference.cjs <fixture-directory>` for
bilingual statement-specific help, three-word commands, exact injectivity arity,
resolved number-set identities, native Unicode aliases, infix union/intersection,
Cartesian product and composition, numerals, preserved tutorial examples, focus,
click/hover consistency and honest unknown-kind fallback. Source and execution
records remain unchanged. The examples are real public CLI inputs. Static
catalogue checks live in `src/reading/test_language_reference.py`; they require
an authored entry for every current statement dispatcher leaf and explicit
associations or gaps for every inventoried object/fact branch. These checks do
not establish complete hover or proof-form coverage.

Generate `--theorems` fixtures and run
`node src/reading/web/tests/theorem-proofs.cjs <fixture-directory>` for bilingual
`by thm` and `release thm` applications. Real exports cover user and builtin
theorems, exact parameter substitution, verified premises, multiple outputs,
generated existential conclusions, definition navigation and return, equality
operator selection, final closed WD and an unproved-premise rejection. Missing
callee, argument, premise or output records must not create guessed bindings
or application provenance. Keyword hover keeps language help together with the
actual invocation; `by thm` and `release thm` remain complete keyword spans.
The two-output release variation reuses the same
public theorem unchanged. This suite does not assert browser geometry or
complete step-by-step coverage of internal theorem derivations.

Generate `--builtin-references` fixtures and run
`node src/reading/web/tests/builtin-theorem-language.cjs <fixture-directory>`
for every authored builtin theorem description. The native checker executes
the exact example displayed in each card. Bilingual public hover, focus, click
and locale changes retain source/evidence and do not reverify. Controls remove
or corrupt native identity/callee data, introduce unknown/prototype variants or
conflicting rule IDs, and retain a real user theorem. Missing catalogue text
does not erase a retained typed identity. Actual rejected calls must not
gain success applications. Static tests independently validate native names,
arity, both languages and wiring; generic labels and unwired cards do not count
as mathematical descriptions. Twenty native rejections cover release/selected
domain failures, arity, shape, order and choice requirements; complete tuple,
Cartesian and function domains; comprehension and structure conditions;
intersection factors; false extrema, empty real sets and strict rational density.
In both languages,
their theorem names retain declaration help through hover/focus and click while
the failed calls gain no success application. Separate controls corrupt/remove
the source declaration type, canonical name, arity and kind; conflict with the
successful application; and retain declaration help without application data.
Nested rejected theorem calls show their retained missing premise once and pin
to the actual failed child. Legacy body evidence, broken parent relationships
and failures on different rows retain their separate reports; matching text
alone cannot merge failures. The test reads the symbol compartment only when
its `hidden` property is false, so whole-row failure hover exercises the actual
proof compartment too. Sequence-limit and finite limsup/liminf rejections cover
missing candidate proofs, invalid domains, nonzero/positivity requirements,
selector evidence, extrema kinds and tail conditions.
Legacy controls remove all new metadata. Native producer acceptance lives in
`cargo test --release --test reading_theorem_symbols` and preserves user,
unknown and qualified-name boundaries. The prime-divisor example is the checked initial
existence/witness portion of its public example, not its later infinitude proof.
The function-space card uses the first active identity-function statement of
its public example. Its longer finite-domain regression remains in the public
file; the card does not claim to execute or display that entire file.

Generate `--objects` fixtures and run
`node src/reading/web/tests/object-language.cjs <fixture-directory>` for 56
newly documented named object operations. Twenty-six real positive sources
cover matrix domains and conjugation conventions, ranges, folds, preimages,
function composition, finite extrema and proof-consuming real selectors. The
suite exercises 112 bilingual hovers, keyboard focus, lexical roles, unchanged
selection and unchanged source/evidence records. Three native rejections cover
fractional summation indices, a noncommutative finite-set fold and an integral
without existence evidence. It does not establish contextual brace anchoring
or complete AST-expression/proof coverage.

Generate `--contexts` fixtures and run
`node src/reading/web/tests/context-language.cjs <fixture-directory>` for 32
bilingual contextual cases from 16 real positive sources. Actual AST-owned byte
ranges distinguish all eight intervals/rays, listed sets, comprehension,
function values/spaces, calls, structures, fields and template instances.
Hover and focus retain selection, symbol definitions and equality proof access.
Controls remove hints, alter source bytes, introduce conflicting/unknown keys,
use invalid byte coordinates or null metadata, and edit checked source. These
must preserve legacy behavior without attributing stale or guessed meanings.

Generate `--multivariable` fixtures and run
`node src/reading/web/tests/multivariable-language.cjs <fixture-directory>` for
all 11 native multivariable selectors and 16 predicates. The existing calculus
example supplies real accepted token spans, with invalid-coordinate and
missing-selection-proof examples as rejection controls. Bilingual hover and
keyboard focus expose the exact signatures and mathematical help, preserve
selection and leave all source/evidence records unchanged. The catalogue tests
compare card arities with the live AST dispatchers and preserve matrix,
second-partial-order and differentiability distinctions. These checks establish
semantic help access, not complete multivariable proof-tree explanations or
browser geometry.

Generate `--symbols` fixtures and run
`node src/reading/web/tests/symbol-language.cjs <fixture-directory>` for named
and postfix factorial, structure prefixes, field access, template instances and
the closed integer-range ellipsis. Bilingual hover/focus checks cover current
and metadata-free exports. Unique existence must keep its distinct `exist!`
card; negative/fractional factorial arguments and an incorrect result remain
rejected. The range tracer uses the public equality-cover example. The older
`test_objs/closed_range.lit` empty-range claim has a separately observed proof
failure and is not used as a passing fixture or pinned as an intended rejection.

Native checks are `cargo test --release --test reading_expression_hints` and
`cargo test --release --lib reading::capture::source_hints::tests`. They check real parsed
AST kinds and exact source slices, Unicode normalization, comment exclusion,
redundant grouping, AST/source occurrence counts and missing locations. Generate
`--repeated` fixtures and run
`node src/reading/web/tests/repeated-language.cjs <fixture-directory>` for both
occurrences of sets, field paths and calls through public hover/focus events.
The function-body/list-set brace boundary remains unassigned when the counts
disagree. These assertions do not claim complete source matching for all
spellings, mixed-role ambiguities, multiline layouts or browser geometry.

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

Generate proof-route fixtures with
`python3 src/reading/web/tests/fixtures.py <fixture-directory> --correspondence`,
then run `node src/reading/web/tests/proof-correspondence.cjs <fixture-directory>`.
Actual public examples exercise known atomic argument equalities, a builtin
atomic rule, a builtin strategy, a named strategy and bilingual syllogisms.
The test follows the exact cited universal and returns to its application,
checks instantiated premise proofs, ordered multi-parameter bindings, visible
nontrivial known-argument equalities, and unchanged reading JSON. Degraded
controls cover wrong universal identity, missing argument/equality records and
incorrect premise-proof pairing. These are public component events, not browser
visual acceptance or an exhaustive grammar/proof-form audit.

Generate `--definitions` fixtures and run
`node src/reading/web/tests/definition-proofs.cjs <fixture-directory>` for
reciprocal and predicate definitions, explicit `by def`, nested and curried
applications, callable aliases, tuple properties and declared codomains. The
suite checks real source citations and return, retained binder names, residual
calculations, final closed WD (including a selected body's narrower guard), and
rejection controls. Removing binders, expansion records or residual facts must
not produce guessed substitutions or proof steps. This exercises the public
DOM component and CLI evidence, without browser geometry or visual assertions.

Generate `--equivalences` fixtures and run
`node src/reading/web/tests/quantified-equivalence.cjs <fixture-directory>`
for quantified equivalences. Both implications retain their native proof-goal
IDs and distinct saved-universal IDs. Public hover, focus, click, citation and
return distinguish shared premises from the two sides' direction-dependent
roles. Cases include several clauses, no quantified parameters, empty carriers,
local theorem scopes, actual forward/reverse proof failures and WD rejections.
Missing/conflicting proof, parameter, clause, scope, store, source and output
records must not fabricate successful correspondence or published facts. The
source gains no rows; results and per-direction WD remain collapsed. Optional
export and project-bundle arguments exercise two real source files through lazy
chunks and direct compilation. A presentation-only metadata control separately
checks retained dependency notices without introducing any Litex assumption.
These tests do not assert browser geometry or
complete coverage of all quantified proof forms.

Generate `--counterexamples` fixtures and run
`node src/reading/web/tests/counterexample-proofs.cjs <fixture-directory>`
for `not forall` proofs. Native cases cover supplied witnesses, builtin
existence, universal instantiation, premises, multiple conclusions, disjunctions,
comparison chains, guarded division, local claims, negated-universal assumptions
and rejected goals. Proof and
published-existential IDs remain distinct; later known-exist reuse cites the
actual inference. Source-clause roles, stable proof/symbol hover, navigation,
return, pending edits and final closed counterexample-formation checks use public
component events in both languages and editor modes. Corrupted records never
invent parameter bindings, witnesses or publication identity. The provenance
notice control changes presentation metadata only, without adding a Litex
assumption. Optional export and project-bundle arguments exercise an explicit
cross-file theorem release and definition navigation through two lazy chunks.
The same-file forall fixture preserves `0 + 1` for native structural matching;
it does not claim new arithmetic argument discovery. These checks do not cover
browser geometry or every negated-quantifier proof form.

Run `node src/reading/web/tests/proof-rules.cjs <fixture-directory>` to check the
actual `ExactIntegerDiv` application for `p / 2 $in Z`, its context, full guarded
law and parameter substitution in both locales. Hovered and pinned views agree.
Exact equality steps retain their own builtin rule/strategy rather than rules
from a premise. Degraded controls remove catalogue metadata or application
identity separately; only the former preserves a recorded rule name. Assumed
and rejected facts must not receive success-rule applications. Full exported
bundles remain unchanged.

Run `node src/reading/web/tests/stable-hover.cjs <fixture-directory>` with the
same actual CLI fixtures to exercise sentence-owned hover and its separate
symbol-information compartment in both locales, in editable and read-only
views. A controlled clock checks dwell continuity, movement between symbols,
retained proof DOM/expanded conditions/scroll, entry across the source/card gap,
cancellation of neighboring-sentence candidates, dismissal, and edit
invalidation. It also checks predicate definitions, compound keywords, exact
equality steps, failed checks and local assumptions. Source bundle JSON stays
unchanged. These are public event tests, not browser layout measurements.

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

`fixtures.py <directory> --foundations-eval` exports the public foundation and
evaluation inputs, their rejection boundaries, strict foundation cases, and
four exact existing native empty-fold/reduction regressions. Run
`node src/reading/web/tests/foundations-evaluation.cjs <directory> [export]`
against these native results. The optional export has the four dispatcher
sources, retained byte-for-byte, in separate chapters. Checks cover bilingual
editable/read-only source interaction, actual rewrite citations and final
publications, foundation applicability versus the foundational principle,
ignored local-store errors, lazy algorithm/function/fold computations, empty
fold identities, final closed WD, navigation and missing/conflicting records.
Computation tapes do not become invented proof Stmts. A source edit invalidates
all old logical results. These component checks do not verify browser geometry.
`cargo test --release --test reading_qualified_eval` separately runs actual
exported/imported algorithm chapters and the out-of-domain rejection. Imported
calls explicitly release their function interfaces and assert their actual
computed values. `cargo test --release --test reading_foundation_interfaces`
checks qualified Zorn interfaces and the undefined/unary relation rejections.
Foundation bubbles also check bilingual carrier/family/predicate roles and
the exact declaration reached from each role. Missing input or predicate
identity must not borrow a same-spelled definition.

Run `node src/reading/web/tests/mathematical-bindings.cjs <directory> [export]`
with the same foundation fixtures to check mathematical names for native
generated binders. Real regularity, choice and Zorn results cover complete
existential conclusions, nested function-domain binders, authored names,
navigation and final closed WD in both languages and editing modes. Altered
payload controls retain raw names when binder/symbol identity is incomplete
or contradictory, and prevent capture of an authored free name. The optional
four-source native export checks lazy loading. Native source/evidence are
unchanged. Premise certificates do not inherit the enclosing foundation
command's axiom label; the actual foundation notice remains visible. These
checks do not establish exhaustive naming coverage or browser geometry.
Known-universal certificates additionally expose their recorded outer-binder
renamings with arrows, distinct from object equalities and instantiation.
Tests follow the actual cited universal and reject incomplete, reordered,
duplicate or foreign parameter IDs and wrong/missing citations.

The native checking transport has separate Rust acceptance:
`cargo test --release --lib reading::compact_json_output::tests` checks streaming
format fidelity, including Unicode, escapes and buffer boundaries;
`cargo test --release --test reading_http --test reading_site` exercises the
actual loopback service, child verifier, cache, failures, policies and exports.
The upload response is compact JSON with complete values; the ordinary CLI
continues to emit formatted JSON.

`atomic-wd.cjs <fixture-directory>` uses real `--lessons --correspondence`
exports to check the final, initially collapsed WD disclosure across known,
builtin, builtin-strategy, named-strategy, universal-instantiation and equality
routes. It opens the actual nonzero-denominator condition and its proof and
checks honest missing-data behavior. `rule-comments.cjs <fixture-directory>`
checks the per-application English/Chinese copy and language switching; older
exports continue to use catalogue descriptions. `cargo test --test
reading_rule_comments` checks the actual Rust capture, including distinct scalar
subrules sharing one catalogue ID. These are data and component checks, not
browser or visual acceptance.
# Conjunction and disjunction proofs

`fixtures.py <output> --binary <litex> --connectives` exports existing Or/And
examples plus Session-verified direct, compound, chain, universal and rejection
controls. Run `node connective-proofs.cjs <output> [two-source-export]
[compiler-project-bundle]` for bilingual editable/read-only public hover,
component selection, temporary-assumption navigation/return, whole-disjunction
citations, equality transport, actual forall bindings, all 18 current Or builtin
rule families, partial failures and missing-record controls. The optional
export uses file-backed lazy loading; the last argument is an actual compiler
POST result. These are content and public-event checks, not browser geometry QA.
Original source and verification/storage/scope records must remain unchanged.
The native whole-And forall route discards separate component formation
certificates; tests require an explicit omission notice rather than invented WD.
## Complete function-domain proofs

Generate `--function-domains` fixtures, then run `node function-domains.cjs
<fixtures> [two-source-export] [compiler-project-bundle]`. The native fixtures
cover all eight current complete-domain source families, both theorem call
forms, both tuple peers, guards, outer-bound domains, empty domains and actual
alpha/two-inclusion comparisons. Complex-valued tuple equality ensures that an
internal return placeholder is never presented as a theorem requirement.
Failure controls distinguish missing interfaces, function/target formation,
arity and inclusion directions from failed return-value premises. Public
pointer events, lazy definition navigation/return and missing/foreign-record
controls preserve original source, facts, scopes and proof records. These tests
do not observe browser geometry. Module examples explicitly release the named
definition; the initial unreleased caller rejection is preserved separately.

## Ordinary function and Cartesian membership

Generate `--function-membership` fixtures and run `node function-membership.cjs
<fixtures> [two-source-export] [compiler-project-bundle]`. Actual native records
exercise all three selected membership owners, complete input interfaces,
alpha-renaming and both inclusion directions, guarded and symbolic inputs,
empty domains, Cartesian aliases and complex coordinates. Every retained
return or coordinate condition opens its own proof. Universal proof variables
and citations remain local, with formation last and closed. Source hover,
editable/read-only modes, both languages, lazy cross-file definition links and
return navigation preserve the input records. Missing, truncated, foreign and
failed evidence controls do not invent a complete derivation. Expected search
misses remain separate from successful explicit intermediate-interface cases;
these tests make no exhaustive native-proof or browser-geometry claim.

## Native matrix function interfaces

Generate `--matrix-membership` fixtures and run `node matrix-membership.cjs
<fixtures>`. Real constructor, transpose, operand, returned-function, alias,
empty-domain and vector cases cover the five native scalar-evidence families.
The tests open complete input interfaces and scalar premises independently,
follow exact equality citations and proof-local input premises, retain stable
symbol help, and keep expression checks last and closed. Wrong domains, extra
guards, non-real-to-real requirements and out-of-range applications remain
rejected. Missing or foreign records do not receive invented bindings or
successful derivations. Both languages and editor modes preserve native input
records. The retained native rule, rather than a second frontend verifier,
owns the accepted domain comparison. No browser geometry is observed.

## Rejected statement headers

Generate `--failed-headers` fixtures and run `node failed-headers.cjs <fixtures>
[failed-two-source-export] [compiler-project-bundle]`. Real claim, nested claim,
case, contradiction, theorem, sketch, universal and formation/parse failures
exercise the distinction between a muted unfinished header and the precise
red failure row. Native body indices and child identities drive navigation;
return restores the same header issue, including same-statement jumps. Goals
stay optional and complete, using an owning typed formula or captured Litex
text. Both languages/modes, keyword compartments, keyboard access, Unicode
source offsets, successful controls and missing/foreign metadata are covered.
The two-source failure retains explicit definition release in the caller. No
proof facts are invented and no browser geometry is observed.

Generate `--inferred-rules` fixtures, then run
`node inferred-rules.cjs <fixtures> [actual-export]` for ordinary inferred
results. Existing strict sources cover predicate domains/definitions, theorem
outputs, set and function carriers, template expansion and cancellation.
Each selected conclusion has its actual native rule and source FactId, with
definition navigation, Back, local scopes and retained side-condition proofs.
The source instance keeps its own direct proof. Result lists and extra rule
conditions start closed. Missing or conflicting origins, rule descriptors,
store effects, source stores, producers and scopes cannot supply borrowed
provenance. Bilingual editor/read-only events preserve the input bundle and
source rows; edits invalidate old explanations. Optional lazy-export acceptance
loads actual native source/proof parts. These tests cover selected native rule
families, not all inference variants or browser geometry.

### Failed claim contexts

Generate `--failed-claim-context` fixtures, then run
`node failed-claim-context.cjs <fixtures> [legacy-fixtures]`. Strict Session
sources cover quantified and ordinary body failures, nested claims, a failed
closing check after a verified prefix, actual premise inferences, successful
local helpers, and failures before entry. Bilingual editor/read-only events
check actual native scopes, parameter domains, assumed FactIds, accepted body
steps, unexecuted suffixes, default-closed local conclusion checks, failure
navigation/Back and edit invalidation. WD-only scope records cannot replace the
actual body scope. Missing or foreign native records do not create assumptions;
an incomplete closing prefix preserves the independently retained context.
Local premise consequences open their own retained rule and source links even
under a rejected claim; the premise and its consequences remain scope-local.
WD-only mentions do not become primary source results when their native scope
is preserved.
Legacy lexical-only scopes receive no invented introduction certificates.
Native producer acceptance lives in `tests/reading_claim_contexts.rs`. This
does not cover every other failed proof-body family or browser geometry.

### Failed ordinary universal proofs

Generate `--failed-universal-context` fixtures, then run
`node failed-universal-context.cjs <fixtures>`. Actual strict Session sources
cover a checked clause followed by failure, no premises, dependent collection
parameters, predicate-premise inference, failure at the first clause, expression
formation failure, a universal inside a failed claim, successful and pre-entry
controls, and the parser's rejection of directly nested universals. Both
languages and editor/read-only modes check actual scopes, local proof links,
default-closed prefixes, exact failure positions, header navigation and Back,
direct proof previews on checked clauses, editing invalidation and unchanged
source/evidence. Mouse hovers and keyboard header previews also follow scope
and premise links and return to the same visible proof, without a stale error
selection. Malformed introductions,
premises, scope/subject/source records fail closed; malformed prefix/failure
correspondence preserves separately retained parameter and premise context.
This does not add native result fields or cover every theorem/strategy failure.

### Exact function interfaces and call-return guarantees

Generate `--function-properties` fixtures, then run
`node function-properties.cjs <native-fixtures>`. The public DOM/event suite
covers known and declared exact interfaces, all retained standard-return rows,
codomain matches versus alternative complete input domains, grouped parameters,
guards, two-layer calls, returned function-space aliases, local premises and
rejected inputs. It checks both languages and editor/read-only modes, real
citation navigation/back, stable symbol help, edit invalidation and final closed
expression checks. Missing or foreign metadata fails closed. Legacy literal
nested signatures have a structural fallback; an aliased second interface is
never resolved in JavaScript. New positive fixtures come from the real compiler.
File-backed tests do not establish browser geometry.

### Local source equality proofs

Generate `--local-source-equalities` fixtures, then run
`node local-source-equalities.cjs <fixtures> [actual-export]`. Strict Session
inputs cover successful and failed universals, checked closing clauses in
claims, theorems and strategies, nested scopes, single equalities, distinct
cited premises and mixed relation chains. Bilingual editor/read-only events
check each adjacent proof, its own context/citations, final closed expression
checks, pinning, keyboard selection, exact citation/scope Back, whole-line reset
and edit invalidation. The bundle and source row count remain unchanged.
Missing, foreign or ambiguous proof/goal/clause/scope/source records cannot
borrow another proof. Definition clauses and unexecuted goals receive no proof
targets. Partial failed chains use their own adjacent-check mapping and are not completed
local clauses.
`LITEX_READER_JS` selects a frozen reader for before/after regression evidence;
the optional export gate uses the actual exported reader. These are file-backed
DOM/event checks and do not observe browser geometry.


### Failed chain proofs

Generate `--failed-chain-proofs` fixtures and run
`node failed-chain-proofs.cjs <fixtures> [actual-export]`. Strict Session sources
cover first/middle/last search failures, mixed operators, direct and entered
universal WD failures, claim closing checks, nested scopes, cited premises and
unchecked suffixes. A claim goal-WD rejection and a predicate declaration are
non-assertion controls. Both languages and editor modes check each actual
adjacent proof/rejection, its own formation evidence, closed prefixes, source
pinning, keyboard access, scope/citation Back, whole-row diagnostics and edit
invalidation. No complete-chain proof or outer publication is manufactured.
Malformed prefix/index, endpoint, source, goal/clause and scope records fail
closed. Missing Normal diagnostics retain the Native search/formation status.
Optional export checks use the actual exported reader; `LITEX_READER_JS` selects
a frozen reader for before/after evidence. File-backed events do not establish
browser geometry or transport-error absence.

Generate `--whole-chain-forall` fixtures and run
`node src/reading/web/tests/whole-chain-forall.cjs <fixtures> [legacy-fixtures]`
for whole-chain known-universal applications. Actual sources cover direct and
later conclusion locations, grouped and repeated parameters, aliases, guarded
mixed chains and longer chains. Controls preserve adjacent fallback, missing
premises and invalid expressions. Bilingual editable/read-only events exercise
per-operator projection, source navigation and exact return, stable sentence
hover, keyboard/pinning, final closed WD and edit invalidation. Conflicting
source, location, argument, match and WD endpoint records remain incomplete.
Legacy native inputs lack retained chain WD and receive that explicit fallback.
These tests do not establish browser geometry or complete language coverage.

Generate `--failed-definitions` fixtures and run
`node src/reading/web/tests/failed-definition-applications.cjs <fixtures> [legacy-fixtures]`
for actual rejected definition checks. The sources cover multiple/dependent
arguments, builtin and user definitions, nested local assumptions, failed
parameter membership, unavailable definitions, goal formation and unchecked
suffixes. Bilingual editable/read-only events validate the actual prefix and
failure, definition navigation and exact return, stable symbol help, final
closed WD and edit invalidation. Missing or conflicting goal/scope/WD/prefix
records do not acquire completed checks. Failed instances are not published.
These are public DOM/content checks and do not establish browser geometry.

Generate `--failed-theorems` fixtures and run
`node src/reading/web/tests/failed-theorem-invocations.cjs <fixtures> [old-fixtures]`
for actual failed theorem lookup/call shape, dependent arguments, complete
function-domain peers, ordered premise prefixes, unchecked conditions and
selection of a target not returned by the theorem. The canonical negative is
`examples/test_statements/negative/by_thm_stmt/retained-invocation-prefix.lit`.
`cargo test --release --test reading_failed_theorems` checks retained producer
records and unpublished failed goals. Public bilingual editor/read-only events
check source navigation and exact Back, actual caller-premise citations, stable
symbol help, final folded domain/formation checks and edit invalidation.
Removed or conflicting argument, store, scope or source records fail closed;
old bundles do not acquire a guessed history. Later derivation, conclusion-WD
and closing-WD failure payloads are retained but currently have no runnable
source acceptance trigger; their complete interactive history is not claimed.
These tests do not observe browser geometry or certify every statement path.

Generate `--failed-contra` fixtures and run
`node src/reading/web/tests/failed-contra-context.cjs <fixtures> [old-fixtures]`
for actual reversed assumptions and local consequences at `?`, completed body
steps, source-owned unchecked suffixes and the two ordered `impossible` checks.
The public negative is
`examples/test_statements/negative/by_contra_stmt/retained-assumption-body.lit`;
`missing-compound-opposite.lit` covers a proved conjunction whose opposite is
not established. The shared closing result also covers atomic case closings.
The tests exercise both languages and editor modes, actual inference citations,
local source navigation/Back, stable symbol help, final folded formation checks,
edit invalidation and missing/foreign/legacy controls. A quantified theorem
premise independently checks retained fact structure with derived display text.
`cargo test --release --test reading_failed_contradictions` verifies the Native
producer and source identities. The existing compound-closing and failure-JSON
Rust suites retain their proof, WD, scope and rollback checks. Failed outer
publication stays empty; actual local steps and assumptions are still visible.
Assumption-WD and final outer-store failure payloads are retained but have no
runnable source trigger in this checkpoint. Browser geometry and exhaustive
failure coverage of all statement families remain unverified.


`failed-object-introductions.cjs` consumes actual Native records exported by
`fixtures.py --failed-introductions`. It exercises grouped nonempty checks,
type preflight, successive value-formation and membership checks, dependent
instantiated carriers, existential goals and source verification before failed
witness naming. It uses public bilingual editable/read-only events, real
citations and definition navigation with Back, stable symbol help, final closed
WD and edit invalidation. Missing, foreign and legacy records cannot acquire a
successful introduction or an invented prefix. The existing introduction suite
continues to cover successful forms; selected fixtures are not exhaustive
coverage of all template, structure-opening or operational-error branches.

### Declaration status

```sh
python3 src/reading/web/tests/fixtures.py <fixtures> --declaration-status --binary target/release/litex
node src/reading/web/tests/declaration-status.cjs <fixtures>
```

The public-event checks cover rejected object, function, theorem and strategy
declarations, accepted global and local controls, valid definitions referenced
from rejected calls, formal parameters and separate induction executions. Both
languages and editable/read-only modes exercise symbol hover, keyboard focus,
selection, definition-check navigation, exact Back and edit invalidation.
Synthetic missing-verdict and conflicting-scope controls check conservative
presentation; they are transport tests, not newly verified mathematical cases.
The source and Native records must remain unchanged. These DOM tests do not
certify browser layout or exhaustive declaration-failure coverage.

### Failed definition checks

```sh
python3 src/reading/web/tests/fixtures.py <fixtures> --failed-interfaces --binary target/release/litex
node src/reading/web/tests/failed-interface-checks.cjs <fixtures> [older-fixtures] [<fixtures>/failed-interface-book]
```

Actual source cases cover parameter-type prefixes, predicate conditions,
struct fields and equivalent conditions, template premises and a value-WD
body failure. Bilingual editable/read-only events inspect completed, failed
and unexecuted source rows, pinning, scoped assumptions, exact Back, final
closed WD and edit invalidation. Missing/foreign controls stay incomplete;
legacy payloads retain their actual diagnostics without invented histories.
`tests/reading_failed_definition_contexts.rs` verifies result ownership and
the separately retained struct field scope. These selected cases do not certify
all struct opening or template body variants, or browser geometry.

Generate `--quantifier-formation` fixtures with an actual release executable and
run `node src/reading/web/tests/quantifier-formation.cjs <fixtures> [older-fixtures]`.
The sources distinguish forall proof introduction from formation-only definition
checks, including a false but well-formed consequent that cannot establish an
instance. Bilingual editable/read-only public events check actual parameter and
premise prefixes, formation-only clauses, failed/unchecked source rows, closed
WD, local inference navigation and Back, edit invalidation, old records and
foreign/missing scope/source/subject/endpoint controls. The native producer gate
is `cargo test --release --test reading_quantifier_formation`; its runtime
checks verify rollback and absence of storage for the false consequent. These
checks are file-backed and do not assert browser geometry.

Generate explicit-assumption histories with
`python3 src/reading/web/tests/fixtures.py <fixtures> --trust-have-history --binary target/release/litex`,
then run `node src/reading/web/tests/trust-have-history.cjs <fixtures> [older-fixtures] [fixtures/trust-have-book]`.
Actual non-strict sources check parameter/body failure prefixes while strict
controls reject before entry. Bilingual public events distinguish formation
from assumptions, verify closed prefix/unchecked/final WD, source pinning, edit
invalidation, missing/foreign records and actual three-source definition/Back
navigation. The producer/rollback gate is
`cargo test --release --test reading_trust_have_history`. These tests observe
file-backed DOM events, not browser geometry.

For the qualified by-definition proof-entry lifecycle, run
`node src/reading/web/tests/qualified-proof-entry.cjs <reading.json> [export-directory]`.
The three-source input and lazy export are generated by `--trust-have-history`
above. It checks the accepted qualified instance before a later source failure,
actual definition-condition proofs, keyword help, inference location, exact Back
and missing ownership. A selected fact opens its pinned explanation; close it
with Escape before expecting a second transient source-hover popup. Both
interaction states are tested independently in Chinese/English and editable/read-only
views. Missing serialized primary/role display fields do not imply missing
proof evidence: the shared reader can derive the view from the actual accepted
statement and retained proof.

For the other quantified formation histories, generate fixtures with
`python3 src/reading/web/tests/fixtures.py <fixtures> --peer-quantifier-formation --binary target/release/litex`,
then run
`node src/reading/web/tests/peer-quantifier-formation.cjs <fixtures> [older-fixtures] [<fixtures>/peer-book]`.
The actual sources cover `exist`, `exist!`, `not exist`, `not forall` and
quantified equivalence. Existential body clauses are locally assumed in order
only for subsequent formation checks; not-forall consequents and equivalence
sides are checked for formation without being assumed true. False but
well-formed sides therefore acquire no fact-proof links.

Top-level negated universals retain their actual counterexample-existential
correspondence. Equivalence proofs retain their actual two-direction
correspondence and, when available, the first completed direction. Fresh derived
IDs are related only through those typed records and their exact child results.
Bilingual editable/read-only events inspect parameter and clause prefixes,
failed/unchecked rows, collapsed WD, scoped inference, three-source lazy
definition navigation and exact Back, edit invalidation and missing/foreign
controls. Legacy records can expose histories they actually retained; terminal
diagnostics alone cannot reconstruct lost prefixes. Native producer and rollback
checks live in `tests/reading_peer_quantifier_formation.rs`. These selected
atomic/equality cases do not certify all compound formation or structure-opening
branches, or browser geometry.

Generate compound quantified formation inputs with
`python3 src/reading/web/tests/fixtures.py <fixtures> --compound-quantifier-formation --binary target/release/litex`,
then run
`node src/reading/web/tests/compound-quantifier-formation.cjs <fixtures> [older-fixtures] [<fixtures>/compound-book]`.
Actual sources distinguish complete conjunctions, comparison chains and
disjunctions from partial component/adjacent/branch checks. A component checked
only for formation is not adopted before the whole clause passes. Disjunction
formation checks every branch even when an earlier alternative is true.

Both native equality-certificate forms are accepted where their actual source
arguments correspond. Stored conjunction components and chain edges keep their
native indices, IDs and scopes; adopting a disjunction does not assume either
alternative. Definition-derived consequences inside a conjunction follow the
actual ordered atomic-inference child and stored component to the resolved
definition. Missing or conflicting histories cannot supply that link. The
source-local quantified card takes precedence over its enclosing definition's
duplicate card only under exact fact identity and native scope ancestry; the
definition header retains its own explanation. These are selected public DOM
checks, not exhaustive nested/structure-opening or browser-layout acceptance.

Use the current public hover protocol and actual retained proof route when
maintaining older drivers. Editable source hover goes through the editor's
pointer target and dwell; symbol help shares the sentence popup. Quantified
formation can fail before a contradiction assumption or counterexample search
is entered. Function-domain failure details remain inside the final, initially
closed formation disclosure. Mutation controls must target the actual retained
`ProofBlockBodyFailed`, including when an enclosing claim now owns its history.

The positive-addition source previously labelled as a builtin strategy now
retains `GreaterFactSearchProofByBuiltinRule::StructuralRealSign`; its two
positive premises must remain cited. `proof-correspondence.cjs` independently
checks a reachable union-membership builtin strategy as well. Lesson citation
checks follow the actual FactId, including when a local assumption precedes
the cited equality in the popup. These checks preserve native verdicts,
publication boundaries and missing/foreign-record rejection rather than
requiring an obsolete card selector or proof route.

Generate ordinary compound inputs with
`python3 src/reading/web/tests/fixtures.py <fixtures> --compound-fact-formation --binary target/release/litex`,
then run
`node src/reading/web/tests/compound-fact-formation.cjs <fixtures> [<fixtures>/fact-formation-book]`.
Actual source cases distinguish pure compound WD prefixes from already-proved
And components and chain edges, including early/late stops, nested Or→And/Chain,
proof-body failures, pre-entry goals, a local universal conclusion and successful
repairs. Truth-search failure before a later undefined expression must not
acquire a check of that expression. Operator-specific failure bubbles retain
only the selected edge's formation checks.

The same public events cover missing/foreign histories, closed final WD,
source/definition navigation and exact Back, lazy chapter loading, stable symbol
help and edit invalidation. The false first predicate instance in the two-source
project is well-formed; the failed disjunction does not prove or publish it.
`failed-chain-proofs.cjs` checks that a failed formation condition is inside the
final disclosure and is never described as a successful WD certificate. These
are scoped semantic/event checks; they make no browser-layout or exhaustive
all-statement claim.

Generate `--atomic-fact-formation` fixtures and run
`node src/reading/web/tests/atomic-fact-formation.cjs <fixtures>` for actual
equality/argument formation failures, predicate signature failures and builtin
predicate-domain checks. The final closed disclosure retains completed domain
checks and the exact unestablished condition. A user predicate's unsatisfied
defining requirement remains a truth-search failure, and malformed syntax
remains a parse failure. Neither acquires a failed formation certificate.

Retained goal subjects place pre-entry `claim` and `by contra` failures on the
question-mark row. Enclosing headers keep their overview and navigation to the
actual failure. Unicode comments and nested blocks do not change that identity;
no goal assumption or outer conclusion is invented. Bilingual editable/read-only
events cover exact Back, editing invalidation, missing/foreign evidence and
successful repairs. Analysis-domain failures without a retained precise
requirement still have an incomplete explanation; these checks do not claim
exhaustive result-variant coverage or browser geometry acceptance.

Generate `--struct-expansion` fixtures and run
`node src/reading/web/tests/struct-expansion.cjs <fixtures> [<fixtures>/struct-expansion-book]`
for nested and parameterized structure definitions. Original UTF-8 source byte
spans supply complete definitions: `Stmt.source_text` can be only a display
header and is not a round-trip source format. The two-source strict project
qualifies the existing examples and keeps their mathematics intact.

The events check actual parameter/field identities, flattened paths, coordinate
indices, field domains, complete defining conditions, default-closed property
and representation disclosures, source/fact navigation and exact Back. Actual
closing proofs can reuse an earlier automatic opening; tests retain that
citation rather than forcing the latest duplicate. Missing/foreign/mismatched
declarations and stores stay unclassified. Bilingual editable/read-only and
file-backed lazy events preserve Native data and source rows; these tests do
not certify every automatic-opening history or browser geometry.

Generate `--automatic-struct-origins` fixtures and run
`node src/reading/web/tests/automatic-struct-origins.cjs <fixtures> [exported-book] [--require-field-anchors]`.
The source cases retain real standalone forall, claim, theorem and witness
introductions, multiple structure parameters, nested/parameterized fields and
ordinary failures followed by successful Session frames. Events follow the
actual automatically opened property (including the earlier cited property),
its assumed parameter membership, logical introduction and original definition.
They cover local nonpublication, folded parameter checks, lazy definition
loading, edit/destroy cancellation and missing/foreign controls. The strict
field-anchor flag requires precise defining-field links on newly generated
data; legacy snapshots retain the whole-definition fallback.

An entered forall whose consequent is ill-defined differs from a pre-entry
claim goal check, even if both diagnostics concern formation. Object type
preflight and unretained failed witnesses are negative controls. The actual
tuple-field witness failures are retained boundaries, not repaired or silently
reclassified as successful witnesses. These cases certify selected entry paths,
not every structure-opening failure or browser geometry.

Generate `--struct-introduction-history` fixtures and run
`node src/reading/web/tests/struct-introduction-history.cjs <fixtures> [exported-book-or-compiler-json]`.
Actual source cases distinguish verified structural declarations, explicit
trust-have assumptions and temporary properties during rejected formation.
They include multiple objects, local scopes, conflicting explicit assumptions,
template parameters/body checks and a compound forall clause. Structural
conditions are grouped separately from explicit body assumptions. Native
memberships, stores, source binders, scopes and exact citation/definition Back
are checked; missing/foreign data, strict-policy and invalid-value controls
cannot invent a completed introduction. The two-source failure book exercises
real qualified rewriting and lazy definitions, including pending responses
after edit/destroy. These checks do not certify every internal opening error
or browser geometry.

Generate `--strategy-body --statement-kinds` fixtures and run
`node src/reading/web/tests/strategy-source.cjs <fixtures> [legacy-fixtures] [exported-book-or-compiler-json]`.
The 52 canonical positive files use their manifest's actual strict policy;
successful input counts alone do not certify every statement's UI behavior.
The strategy events check ordered executed source steps, nested claims,
shadowed local objects, actual existential certificates, definition conditions,
citation and exact Back, plus bilingual editable/read-only operation and edit
invalidation. Failed and legacy source-only bodies cannot borrow successful
executions. The two-source book follows the actual qualified predicate
definition through file-backed lazy loading. These checks preserve source and
Native identities; they do not certify every failed-body prefix or geometry.

Generate `--failed-strategy-context` fixtures and run
`node src/reading/web/tests/failed-strategy-context.cjs <fixtures> [legacy-fixtures] [exported-book-or-compiler-json]`.
Real final/body failures preserve arbitrary parameters, adopted premises,
completed body steps and checked conclusion prefixes. Later conclusions and
unexecuted statements remain unchecked; the failed strategy is unregistered.
Events follow the actual local hypothesis, failing source goal and qualified
predicate definition with exact Back, in both languages and editable/read-only
views. Controls reject missing or foreign owners, scopes, parameters, premises,
goals and checks. A source occurrence locates its row by authored UTF-8 byte
offset; selecting a symbol shows its definition beside the current source,
and its definition occurrence explicitly navigates to that source. File-backed
lazy tests exercise this distinction. Empty-domain success, pre-entry formation,
duplicate-name parsing and legacy histories are independent boundaries. These
checks do not certify every partial introduction, generated failure or geometry.

The inference-scope tracer distinguishes a temporary formation batch from the
actual proof batch even when they share a seed identity. The viewer events use
the body's retained infer reference and exact conclusion IDs, then follow the
real local consequences and their rules. Scope regressions also check that a
successful definition proof keeps its published consequences in the outer scope.


### Rejected theorem-definition contexts

```sh
python3 src/reading/web/tests/fixtures.py <output> --binary <release-litex> --failed-theorem-context
node src/reading/web/tests/failed-theorem-context.cjs <output> [legacy-fixtures] [qualified-book-export-or-json] [reader-source]
```

The actual Session-derived sources cover direct and universal goal failure,
checked body/final prefixes, a nested failed claim, conjunction/equality-chain
goals, real inferred premises, pre-entry formation and unsupported-goal
controls, same-name recovery and a qualified two-source book. The driver
checks bilingual editable/read-only source hovers, actual local assumptions,
closed conclusions/formation checks, real definition/citation navigation and
exact Back, edit invalidation and nonpublication. Missing/foreign records and
legacy Native without history must not borrow assumptions. The optional reader
source supports a regression check against the preserved previous viewer.
These tests do not certify untriggered parameter-entry, operational or
post-proof storage failure paths, nor browser geometry.

### Goals not reached after a local proof stops

```sh
python3 src/reading/web/tests/fixtures.py <output> --binary <release-litex> --pending-goals
node src/reading/web/tests/pending-goals.cjs <output> [qualified-book-export-or-json] [reader-source] [legacy-fixtures]
```

Actual claim, theorem and strategy inputs distinguish body interruption,
completed/failed final checks and later unchecked conclusions. The source
row's neutral annotation opens the actual context and stopped check with exact
Back and keyboard access. Both languages and editable/read-only views preserve
source rows, facts, scopes and evidence. Editing invalidates the old status.
Malformed prefixes, foreign identities, absent history, formation failures,
successful proofs and actual contradiction/case assumptions cannot acquire a
pending-goal proof or assumed fact. The qualified two-source book uses actual
lazy exports; a compiler JSON argument exercises the same source interaction
with actual POST results. The optional legacy directory must contain genuine
historical Native records. Shared-row/generated goals and browser geometry
are not certified by these selected source cases.


### Rejected relation-law contexts

```sh
python3 src/reading/web/tests/fixtures.py <output> --binary <release-litex> --registration-failures
node src/reading/web/tests/registration-failures.cjs <output> [qualified-book-export-or-json] [reader-source]
```

The actual sources cover all three failed registration laws, a ternary cyclic
permutation, a nested failure with Unicode source comments, an unmet real-domain
requirement, and successful registrations. Shape/domain-spelling, extra-body
and arity controls remain distinct from an entered law check. The real-domain
example enters a universal proof but cannot prove the predicate instance for
an arbitrary set; it is not a pre-entry WD fixture.

Bilingual editable/read-only events check actual parameter and premise IDs,
explicit nonregistration/nonpublication, folded premise inference and its rule,
precise header/failed-target navigation and Back, source editing and Native
invariance. Ordinary premise selection retains its own quantified parameter
frame without repeating the selected premise. Malformed/foreign histories do
not invent local checks. The optional qualified two-source book is exercised
through real file-backed lazy exports or actual compiler JSON. These selected
histories do not certify every partial-introduction failure, later registered
property-use route, generated context or browser geometry.


## Registered and builtin transitivity

```sh
python3 src/reading/web/tests/fixtures.py <output> --binary <release-litex> --transitivity-applications
node src/reading/web/tests/transitivity-applications.cjs <output> [qualified-book-export-or-json] [reader-source]
```

Sixteen real-source cases distinguish registered transitivity, four builtin
order variants, a definition-checked residual, multiple targets, local successful
prefixes of a rejected theorem, global and inferred left premises, and deletion
or search-boundary controls. Bilingual editable/read-only events follow the
actual left premise and definition condition, check inference provenance, pin
and return to the exact source target, and invalidate cards after editing.
Each proof retains its final closed formation checks. Thirty-two malformed
controls corrupt authoritative identities, owners, scopes, endpoints or residual
proofs. The qualified book is checked through file-backed lazy exports or actual
compiler JSON. It registers the property in its caller chapter. No test invents
a chosen registration-source citation or claims browser geometry.


## Proof-command addresses independent of fact provenance

```sh
python3 src/reading/web/tests/fixtures.py <output> --binary <release-litex> --statement-kinds
node src/reading/web/tests/proof-invocation-addresses.cjs <output> [reader-source] [qualified-book-export-or-json]
```

The existing canonical block `by def:` and bare `release thm` sources exercise
the missing header addresses. Bilingual editable/read-only pointer, keyword and
keyboard hover check actual arguments/conditions, final closed WD, pinning,
definition navigation, exact Back, retained goal-row proofs, canonical fact
provenance and edit invalidation. Twenty-four controls corrupt execution kind,
status, source span/line/token, scope, output or proof/call records. Two positive
controls retain actual returns when no new FactId is published. An optional
two-source book loads real lazy exports and follows qualified definitions and
reused conclusions. It verifies that returning restores the invoking source,
statement and line. No test claims browser geometry or exhaustive language
branch coverage.


## Scoped citations in user and builtin definitions

```sh
python3 src/reading/web/tests/fixtures.py <output> --binary <release-litex> --definition-scopes
node src/reading/web/tests/definition-scopes.cjs <output> [reader-source] [qualified-export-or-json]
```

The maintained source directory covers actual subset/superset, proper relations,
injective/surjective/bijective, choice-function, divisibility, coprime and user
definition proofs. Its ordinary prime computation is a control, not a certified
Prime-definition route. The canonical finite-subset check follows a real local
inference and its parameter-domain origin, then returns to the exact source.
A separate structural-sign rule keeps both actual external premises and its
rule name. Bilingual editable/read-only events retain every requirement and
child proof, final closed WD, citations and edit invalidation without changing
Native data. Missing requirements/proofs, mismatched counts/subjects and missing
payloads remain incomplete. The qualified book copies the previously checked
canonical sources and calls; it loads real exports or actual compiler JSON.
These selected variants do not establish all builtin-definition/result branches
or browser geometry.

## Several conclusions from one theorem call

```sh
python3 src/reading/web/tests/fixtures.py <output> --binary <release-litex> --theorems
node src/reading/web/tests/theorem-conclusion-groups.cjs <output> [reader-source] [<output>/theorem-group-book]
```

The actual two-output theorem and canonical `ReleaseThmStmt` example check one
application card, all returned identities, one final closed WD disclosure,
shared argument checks and individually paired conclusion checks. Bilingual
editable/read-only pointer, keyword, keyboard, pin, definition, each output,
exact Back and edit events preserve source addresses and Native records.
Single builtin existential returns keep their inferred consequences separate;
later use keeps its own proof route. Missing, foreign and swapped records
cannot supply another conclusion's formation proof. The two-source book was
accepted in one strict Session and covers qualified, nested and repeated calls,
lazy loading and actual compiler JSON. The older viewer is a negative control
for the duplicate invocation. These checks do not certify every result branch
or browser geometry.

## A universal equality followed by symmetry

```sh
python3 src/reading/web/tests/fixtures.py <output> --binary <release-litex> --forall-equality-symmetry
node src/reading/web/tests/forall-equality-symmetry.cjs <output> [reader-source] [<output>/forall-symmetry-book]
```

Actual Native certificates cover direct and conditional universals, equal
function heads, conjunction components, individual chain equalities, a checked
local prefix of a rejected theorem and the maintained public tracer. Pointer,
keyboard, equality-click, pin, citation, exact Back and edit events run in both
languages and editable/read-only modes. Missing prerequisites and ordinary
forward/arithmetic proofs cannot be relabeled as symmetry. Missing, foreign,
swapped and mismatched citation, source, argument, requirement and reversed
endpoint records remain incomplete. The intermediate equality does not acquire
an invented stored-fact link. Own WD remains final and closed.

The qualified two-source book uses the existing `release obj def` interface
before applying an imported arbitrary function. Its actual universal premise
is local to the caller; following the function declaration loads the first
source and Back restores the exact equality. This does not certify a different
source's unloaded universal or ordinary-source registered Ref/Sym reachability.
The nominal numeric `via_symmetry.lit` example is an arithmetic-route control,
not a certificate for this branch. No browser geometry is claimed.

# Forall equality indexing and rigid argument transport

Status: implemented; correctness, source lifecycle and candidate scaling accepted.
Uniform overall geo speedup is not established.
Date: 2026-10-06 (Asia/Shanghai).
Classification: `kernel_problem` (automatic matching and search cost). The old
failure was a missing automatic route, with an already checkable explicit proof.

The maintained [tracer](../../equal/by_known_forall/rigid_application_alias.lit)
keeps the exact former failure as comments and the same source active. The
reference executable rejects it at proof search with no session error; the
candidate accepts it. Its typed kernel test checks the actual forall source
FactId, instantiated parameter-type obligation and the existing `f(0)=g(0)`
Direct path. Removing that premise still rejects the transport. No trust or
function equality `f=g` is introduced.

## Implementation contract

`KnownForallConclusionMemory.by_equal` owns derived typed trie metadata for
both equality endpoints, replacing the complete equality-cite enumeration.
Only source cites leave the index. Fixed constructors, operator variants,
qualified owners, function prefixes, curried groups and parameter holes are
classified while recording. Committed chain projections survive merge;
failed claims and sketches discard local entries. Cites retain source order.

A rigid argument relative to the cited forall's parameter IDs first consumes
whole-value Direct equality. On a miss, supported constructor children use
Direct leaves. Function prefixes are checked before arguments while the old
flattened certificate child slots are retained. Instantiated types and domain
facts remain required. No AST or Runtime layout was edited by this task.

Retrieval remains conservative. Binder bodies are opaque and still undergo
complete alpha/capture checking. Closed goals retain both structural syntax
and value keys. Already-bound expression fallback is retained, for example
`f(t)=t+1` applied to `f(1)=2`. The index accounts conservatively for the
matcher's suffix-group visitation order and reached binder peers connected
through Direct alpha paths. A routing hit never supplies these proofs.

Scope graphs are borrowed during candidate lookup. Views/aliases and failed
Direct comparisons have a local operation lifetime. The lazy matching graph
and miss memo reset before broader requirement verification; no Runtime cache
or wider leaf search permission was added.

## Executed functional gates

- Release library `forall` filter: 58 tests passed, including 10 new groups.
- Producer/consumer union: 237 distinct release Rust tests passed, including
  141 statement transaction tests, strategies, compound/binder consumers,
  known search, type boundaries, JSON acceptance and replacement uniqueness.
  Two initial empty filters are explicitly excluded from that count.
- Five maintained known-forall equality/atomic files and the newly added Manual
  fence pass the actual CLI with `success=true`, no session error and exit0.
- Metadata scaling: at 100, 1,000 and 10,000 distinct fixed heads, the exact
  goal selects one cite. The same-left/different-right controls also select one.
  At those counts, genuinely generic two-parameter rules retain every cite.
  These are metadata controls, not trusted runtime mathematics.
- Reference retrieval is compared with the real argument matcher, alongside
  numeric/radical/complex, carrier rejection, curried heads, repeated parameters,
  nested congruence, qualified ownership and real proof-evidence controls.

The exact commands, source fingerprints, test names, executable hashes and
performance inputs/results are in the
[durable receipt](../../../../docs/audits/forall-equality-index-2026-10-06.json).
The [approved design](../../../../plan/forall-equality-structured-matching-2026-10-06.md)
records the baseline and compatibility refinements.

## Performance scope

Sequential frozen-executable comparisons completed all intended positive inputs
and the deliberately rejected framing control. Other compiled source is identical
between reference and candidate. After concurrent changes to 16 other source
files, a fresh release build, 237 distinct Rust tests, five maintained CLI files
and the changed Manual fence also pass. Source remained stable through that
final live gate; this task's eight implementation files are unchanged from the
performance snapshot.

| Full176 context | Original forall algorithm | New index/matcher |
| --- | ---: | ---: |
| Prefix replay wall time | 530.73 s | 492.95 s |
| Scalar helper | 4.75 s | 5.13 s |
| Cost35 geometric control | 34.97 s | 41.01 s |
| Optimized vertical proof | 47.11 s | 51.86 s |
| Entire session CPU (prefix + controls) | 562.04 s | 557.14 s |
| Entire session wall | 618.12 s | 591.46 s |

The prefix wall time falls about7.1%, but total CPU falls only0.87% and the
geometric controls include regressions. Dependency51 prefix wall time also
regresses24.88->42.54 s, with more scheduling delay (total CPU103.45->107.42 s).
Small scalar timing is essentially unchanged0.877->0.875 s. A single ordered
trial on a shared host does not establish a major or uniform overall speedup.
The observed full-context concyclic-determinant step48.99->23.76 s is a
statement wall-time observation, not function-level CPU attribution.

The original all-equality enumeration is removed and fixed-head scaling is
verified. Further stage-level geo cost attribution/optimization remains open.
The first candidate and a mistaken earlier old-CLI run are retained separately
and excluded from accepted performance claims. These measurements cover
persistent REPL replay, rather than a cold file batch or every geometry module.

The probe `f(t+1)=t` against `f(2)=1` retains an old automatic-route miss; its
mathematical conclusion is valid under the stated universal premise. This
work does not add inverse substitution discovery. Binder bodies retain opaque
index branches and complete matcher guards. There is no Lean replay claim.

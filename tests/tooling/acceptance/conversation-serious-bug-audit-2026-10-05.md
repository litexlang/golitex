# Conversation serious-bug closeout audit — 2026-10-05

The maintainer requested a consolidated serious-bug report and authorized
bounded local repairs. This is an L4 Rust/system checkpoint; implementation
changes are two parser validations/resolutions with existing types and state.
Exact old/new Litex inputs and the surviving assertion are in the
[source-owned record](../../../examples/test_statements/experience/problem_notes/conversation-serious-bug-audit-2026-10-05.md).

## Actual final gates

| Gate | Observed result |
| --- | --- |
| Release production build | exit 0 |
| Complete Rust lib, all-targets | 933 passed / 1 failed / 934 selected; exit 101 |
| Rust integration | 1 passed / 0 failed |
| New reserved-binding Rust regressions | 4 / 4; also included in the final complete gate |
| New qualified-struct launcher regressions | 4 / 4; also included in the final complete gate |
| Stmt manifest | 50 leaves, 378 / 378, 0 gaps |
| Basic semantic manifest | 175 / 175 |
| Obj inventory and executable files | 99 positive files / 666 assertions; 309 negatives; 0 mismatches |
| Additional production CLI positive/negative controls | 49 / 49 expected outcomes |
| Stable strict file tracers | 5 / 5; actual nonzero statement selections |
| Qualified struct project | strict `-r` succeeds; Rust verifies all four mounted files |
| Migrated original dependent-have / index-cart files | 2 / 2 |

The main binary target has zero unit tests; the lib and integration targets
have the nonzero selections above. The complete gate remains red, with the
same existing DEC04 unused-K expectation as before this task. No negative was
removed or weakened. The existing function-body negative still requires
ordinary proof/WD rejection and a usable session, after replacing its reserved
set parameter Z with the fresh name W.

The Obj driver loads the owning `examples/test_objs/run.py` audit/evaluator and
uses the frozen binary directly. The public runner otherwise rebuilds the
default target and has no binary override. All 408 actual files run; the
manifest has no gap entries. Stmt and basics use their ordinary public runners.

## Repairs and serious-invariant controls

- LEG30: the shared parser binding wrapper rejects object-primary builtin
  spellings before allocating IDs. Native constants and constructors, similar
  user names and rollback are preserved. All three code-source contexts run
  through `Runtime.run_litex_code` and observe Normal/Detailed results.
- LEG27: struct views reuse the existing canonical module/export name resolver.
  Full owner identity, generic domain/arity and current/flat export contracts
  remain intact. Real configured import/file/root execution tests reject wrong
  carrier/field/path controls without an InternalBug.
- Five pre-existing test consumers used reserved sign/i/C/Z names. Only those
  authored names were migrated; the cases, dependencies, values and negative
  checks remain. Two fixture files are also run directly through the CLI.
- The full gate includes cold/warm strict direct and transitive trust-cache
  rejection, valid import cache controls, failed-binding rollback, internal
  conflict diagnostics and the existing guarded arithmetic/complex regressions.
  Production controls include false theorem, wrong witness/OR branch,
  division without a guard, complex/real square boundaries and scope leakage.
  Prior field-preimage and positive-power tracers also pass.

No protected Stmt/Obj/Fact/Env/Runtime fields or state were changed. No general
NotFact, Cartesian enumeration, new trust or global proof-search policy was
introduced. Other sessions' development changes remain intact.

## Binary and source identity

| Production CLI | SHA-256 |
| --- | --- |
| Initial | `96faac20863a4c694d04fbe92f3e86ad3323c2040d92489cc40e352ef8898270` |
| First repaired | `1d7bda24fb3c504bd8fb8af38b7df688d709dc33f86be5fd775022e133f5cd2a` |
| Final pinned | `dddc1902feee4bbdfd163994ed84aef4867ea447041184f680d1d24b87f55b8d` |

Initial complete lib inventory was 915 (914/915), final inventory 934.
Eight added tests are this task's two groups; eleven are shared development
between checkpoints. This is not one unchanging global-tree baseline.
The final production build and first complete test capture use identical
watched source maps. Five consumer renames then change three test-only source
files and two Litex fixtures; record-end production build returns the exact
same binary bytes. Every recorded final build/gate has zero source drift within
its capture interval. Full before/after hash maps and intervening changes are
preserved in raw records; a scoped stable gate does not validate future edits.

The capture watch includes src, tests, docs, Stmt examples, existing hard-error
module fixtures, Cargo manifests and root README. It is not a hash inventory
of every file in the repository. Object fixtures have per-input hashes, and
new configured fixture/tracer bytes are archived separately. Original pre-task
source bytes for the repaired parser files match the recorded HEAD and are
preserved; other initial shared files have their hash maps/binary, not a claimed
complete historical source archive. Git HEAD at report time is
`7c1cdc4866eb2084198d88d533e80c80f397edad`.

## Failed attempts and corrected expectations

All these attempts are retained, rather than hidden behind the final numbers:

- The first basics command used a nonexistent manifest path; the corrected
  `release_basics/cases.json` ran 175 checks.
- Initial core probe expectations incorrectly rejected `0^0=1` and assumed
  bare `e!=0` search. The current Manual explicitly defines the former; the
  checked author route `e>1; e!=0` passes. Initial raw expectations are retained,
  and the final 49 controls use those actual contracts.
- A reserved-binding test first called a string method on a typed session
  error, causing E0599. It was corrected to inspect Debug output. Its next
  attempt demanded the reserved-name diagnostic for `have cart R`, which
  already rejects at the removed-construct dispatcher. The test now uses the
  actual common binder path `forall cart R:`; all 20 names remain executable.
- Qualified fixture drafts initially had `Tagged<R>=` lexical ambiguity,
  flattened access to a multi-export module, and duplicate declarations in an
  ordered export. These invalid setups were corrected. Full and flat paths
  now have actual valid positives and nearest executable negatives.
- Chained nested field value equality search fails in both qualified and
  plain controls even after explicit struct-member/release steps. Declared
  nested field membership succeeds. The original equality is retained as a
  search-limit observation, not reported as a repaired capability.
- First final complete Rust gate was 928/934 with six failures. Five were
  reserved-name authoring consumers; the migration above restores their real
  proof/WD checks. Its full stdout is preserved. A progress message initially
  described the failure count from the tail too early; it was corrected after
  inspecting all six failures, and final counts above use the actual summaries.

## Surviving result and scope

Only the existing unused-K negative assertion fails. Both Point instances
currently define the same R × N field set; no new false numerical theorem or
trust bypass was demonstrated. Its original negative remains present. The
existing source-owned boundary and canonical DEC04 record are retained; this
turn does not reopen a semantic permission question or alter representation.

This checkpoint found no surviving serious false-acceptance, strict bypass,
crash or scope-leak defect in its tested scope. It does not claim complete
release readiness: complete showcases/geometry/textbooks/Lean, all docs
collectors, every builtin branch and independent evidence replay are outside
this gate. Known mathematical feature/search gaps stay in their existing
source-owned/canonical records.

The neighboring machine receipt records gate identities and raw archive
SHA-256, entry hashes and CRC validation. The ignored
`conversation-serious-bug-audit-2026-10-05_receipts.zip` preserves pinned binaries,
exact probes, fixtures, source snapshots, stdout/stderr, failed attempts and
the completed SOP. Only this task's draft directory and ledger are cleaned.

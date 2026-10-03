# Compound impossible: local closing implementation

Task: maintainer-approved `ByContraStmt.impossible_fact: AtomicFact -> Fact`,
2026-10-03. Category 2: local parser/closing/proof consumer repair. No generic
NotFact, Fact payload change, ByCases AST change or Runtime/Env state change.

## Observable change

Before, this complete contradiction was rejected at the compound tail:

```litex
by enumerate finite_set:
    ? forall x {0}:
        x != 1
by contra:
    ? not exist x {0} st {x = 1}
    obtain a from exist x {0} st {x = 1}
    a != 1
    impossible a = 1
by contra:
    ? not exist x {0} st {x = 1}
    impossible exist y {0} st {y = 1}
```

The current parser preserves the complete Fact. The closing helper verifies
that Fact and separately constructs and verifies its existing classified
opposite. Verification failure cannot supply either side. Both typed proofs
remain in the result; Detailed JSON exposes them under `closing`. Names and
reverse assumptions remain local, and failed blocks publish no goal.

[Maintained tracer](../../../stmt_nodes/by/by_contra_compound_impossible.lit)
also executes a multiline forall tail and subsequent goal reuse.
[Focused actual-execution tests](../../../../tests/unit/execute/contra_compound_closing/tests.rs)
cover all ten root families, false/partial/missing proofs, undefined divisions,
nested-quantifier rejection, scope rollback, known IDs, JSON, source replay and
induction parameter recovery. Iff source replay additionally restored the
mandatory `=>:` marker when the forall has no premises.

## Representation and consumers

- And/Or/Chain opposites retain the whole formula. Unique-existence negation
  says every satisfying candidate has a distinct satisfying alternative;
  ordinary nonexistence alone would miss multiple witnesses.
- Forall/iff quantified premises or conclusions cannot be stored in the
  existing QF-only counterexample payload. This is a surviving discussion
  boundary; the implementation rejects it explicitly.
- IR/readable source uses the existing Fact rendering with the whole tail
  indented. Knowledge-base DefinitionMemory caches theorem interfaces and
  clears proof bodies; this field creates no new persistent codec shape.
- No Rust Lean compiler consumer of ByContraStmt exists in this source tree;
  this change does not claim new Lean compilation support.
- Arbitrary flat Boolean normalization can still cost exponentially many
  branches. No unrequested global search rule or silent cutoff was added.

## Acceptance

The new tracer failed at the compound tail in the pinned before binary and
now succeeds. No trust was inserted. The controlled snapshot passed:

- 29 focused tests (17 classified negation, 12 compound closing).
- 377 statement-suite checks across all 50 leaves, zero mismatches or gaps.
- 41 native checks, including eight feature files and four Manual fences;
  three Detailed closing results retain both successful proofs.
- Persistent CLI session: accepted source commits, failed closing does not
  publish `1 = 2`, and the closing binder name can be reused outside.
- Actual-AST integration: 1 passed. Registered example filter: 5 passed.
- All 38 knowledge-base tests selected by the full gate passed.

The full kernel gate reports **618 passed / 3 failed**; before reports
606 / 3 with identical failed test names. The full Markdown runner checks
409 fences; 131 fail, all in the same two historical audit reports. Normative
docs and every directly changed contra snippet pass. The existing broader
WD, projection, audit and atomic-nondeterminism issues remain open in their
corresponding folders.

The final workspace cannot currently compile: unrelated incomplete edits to
`verify_state.rs` define a second VerifyState and omit a comma. No workspace
file was reverted. The acceptance snapshot replaces only that file with HEAD;
all task-owned Rust matches the snapshot exactly. Later concurrent `in_fact`
changes are outside that snapshot. These results therefore establish the
controlled local change, not final compilation of the entire live workspace.

[Before receipt](../../proof_journals/by_contra_compound_before_2026-10-03.json),
[snapshot/substitution receipt](../../proof_journals/by_contra_compound_snapshot_2026-10-03.json),
[shape audit](../../proof_journals/by_contra_compound_shape_audit_2026-10-03.json),
[native/session proofs](../../proof_journals/by_contra_compound_native_2026-10-03.json),
[statement suite](../../proof_journals/by_contra_compound_statement_suite_2026-10-03.json),
and [aggregate acceptance](../../proof_journals/by_contra_compound_acceptance_2026-10-03.json)
preserve actual outputs, commands, source/binary hashes and precise boundaries.
The initial native harness attempt is retained separately: it incorrectly
kept the now-accepted compound-tail expectation and used unsupported empty
`-e`; correcting those test-driver inputs produced the checked final result.

Remaining quantified-representation decisions are in
[the open limitations](../../bugs/by_contra_stmt/limitations.md).

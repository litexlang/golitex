# K005: classified negative-existence contradiction

Task: statement regression suite and explicit by-contra repair, 2026-10-02.
Scope: golitex / NotExist target, proof scope, and genuine closing evidence.
Repair ownership: category 2, completed local Rust semantics using unchanged AST/state contracts.

The original mathematical conclusion is now proved without trust:

```litex
by enumerate finite_set:
    ? forall x {0}:
        x != 1
by contra:
    ? not exist x {0} st {x = 1}
    obtain a from exist x {0} st {x = 1}
    a != 1
    impossible a = 1
not exist x {0} st {x = 1}
```

Active regression: [finite-negated-existence-by-contra.lit](../../boundaries/finite-negated-existence-by-contra.lit).
Enumeration, contradiction, and final citation all succeed in strict mode.

The prior helper rejected every non-atomic target. It now constructs the existing
positive Exist reverse assumption for a NotExist goal, with a fresh wrapper ID.
The existing WD, assumption storage, obtain, two-sided atomic closing and scope
pipeline checks the proof. Only the target is published; reverse assumptions and
witnesses stay local. No Stmt/Fact fields or Env/Runtime state were changed.

[Native acceptance](../../proof_journals/by_contra_classified_goals_2026-10-02.json)
retains exact sources, commands, binary/source hashes and results. Unit tests
also verify retained local evidence, fresh reverse ID, final citation, failed
proof rollback and witness-name reuse. False conclusions, a real witness,
missing universal exclusion and wrong carriers reject. Existing atomic contra
and Fact cases remain selected for the suite gate.

The unchanged [bare assertion](../../boundaries/finite-negated-existence-automatic-search.lit)
still rejects in search_proof. The maintainer accepts an explicit proof and does
not require automatic forall-not to not-exist search. This is a documented
capability boundary; it is not a remaining K005 bug.

[Prior records](../../proof_journals/k005_prior_records_2026-10-02.json) preserve
the old README, reproduction and output before the open folder was removed.
The initial failed explicit proof remains in its original clarification journal.

Broader all-fact contra work is [separate and unfinished](../../bugs/by_contra_stmt/limitations.md):
compound impossible fields need concrete AST approval; exist!/iff/nested forall
still need classified constructions. Closing K005 does not claim that feature complete.

# Registered property Detailed evidence — 2026-10-05

The three registration statements already verify their law. Their Detailed
projection used to discard `prop`, `forall_proof`, and the typed failure stage.
The projector now reads those existing results. No proof rule, result layout,
registration state, or supported syntax changes.

```litex
prop same(x,y set):
    x=y
register symmetric:
    ? forall x,y set:
        $same(x,y)
        =>:
            $same(y,x)
```

Before: `{"success":true,"kind":"register"}`. Now: the same accepted
statement identifies the symmetric property and its predicate, and retains
the actual checked `forall_proof`. English and Chinese gates check the child
proof and confirm that `local_env` stays omitted. Failed undefined predicates,
wrong arities and false laws retain their actual failure payload. Invalid
surface shapes are rejected during parsing, before a register result exists.

The [persistent tracer](../../register/registered_property_evidence.lit) passed
`target/release/litex -strict -f` on the frozen repaired build. Nine focused
Detailed module tests passed, 858 were not selected. Twenty-eight old/current
source pairs preserve explicit legacy registration spellings; current normal
and Detailed outcomes agree before/after the projection repair. One additional
source is the complete prefix author route without registration; both versions
and both current snapshots accept it.

Existing `atomic/by_known_rewrite` examples won earlier definition/known-fact
routes. They do not establish dynamic coverage of registered rewrite variants,
and that other projector remains unchanged. `try:` is unsupported by this
current public Runtime parser; three stopped diagnostic sessions are retained
as parser/setup failures, not mathematical rejection or rollback coverage.

See the [audit](../../../../plan/迁移的plan/legacy-registered-property-audit-2026-10-05.md)
and [full journal](../../../../plan/迁移的plan/proof_journals/legacy-registered-property-audit-2026-10-05.json).

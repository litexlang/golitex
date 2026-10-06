# Fixed interval consumers and numeric subterm priority (2026-10-06)

Task: the authorized broad legacy/current audit, with local BR/WD/straight-bug ownership and protected AST/state contracts. This record accepts two repairs, not the entire legacy migration.

```litex
# Tracer: actual written principal pi bounds.
# Before: legacy accepted; current search rejected the exact source.
# forall y R:
#     -(pi/2)<=y
#     y<=pi/2
#     =>:
#         arcsin(sin(y))=y
# Now: same fact, checked at inherited permissions, with actual bound citations.
forall y R:
    -(pi/2)<=y
    y<=pi/2
    =>:
        arcsin(sin(y))=y

forall y R:
    y>=0-pi/2
    pi/2>=y
    =>:
        arcsin(sin(y))=y

forall y R:
    -(pi/2)<y
    y<pi/2
    =>:
        arctan(tan(y))=y

# Boundary: wrong/missing bounds, closed tangent poles and free-angle mismatches reject.
# No arbitrary expression normalization, search reset or fact publication by the helper.
# Gate: target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_rule/arcsin_principal_bound_spellings.lit
# Tests: cargo test --release --offline --lib trig_interval_bound_spellings_tests
# Owner: src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equality_by_builtin_rules/by_inverse_trig.rs
```

```litex
# Tracer: actual written principal pi bounds.
# Before: legacy accepted; current search rejected the exact source.
# forall x R:
#     -(pi/2)<x
#     x<pi/2
#     =>:
#         cos(x)!=0
# Now: same fact, checked at inherited permissions, with actual bound citations.
forall x R:
    -(pi/2)<x
    x<pi/2
    =>:
        cos(x)!=0

forall x R:
    x>(-1)*(pi/2)
    pi/2>x
    =>:
        cos(x)!=0

forall a,b R:
    -(pi/2)<=a
    b<=pi/2
    a<b
    =>:
        sin(a)<sin(b)

# Boundary: wrong/missing bounds, closed tangent poles and free-angle mismatches reject.
# No arbitrary expression normalization, search reset or fact publication by the helper.
# Gate: target/release/litex -strict -f examples/proof_nodes/atomic/by_builtin_rule/cos_nonzero_principal_bound_spellings.lit
# Tests: cargo test --release --offline --lib trig_interval_bound_spellings_tests
# Owner: src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_rules/not_equal.rs
```

```litex
# Tracer: whole known numeric subterms precede their children.
# Before: this exact claim intermittently failed under frozen before/after binaries.
# claim:
#     ? forall a,b R:
#         a=0
#         b=pi
#         =>:
#             cos(b)<cos(a)
#     cos(a)=cos(0)=1
#     cos(b)=cos(pi)=-1
#     cos(b)<cos(a)
# Now: one structural pass selects the actual whole numeric equality and cites it.
claim:
    ? forall a,b R:
        a=0
        b=pi
        =>:
            cos(b)<cos(a)
    cos(a)=cos(0)=1
    cos(b)=cos(pi)=-1
    cos(b)<cos(a)

# Boundary: wrong numeric conclusions, failed-source reuse and implicit partial-operation WD reject.
# Gate: target/release/litex -strict -f examples/proof_nodes/atomic/by_builtin_rewrite/closed_numeric_subterm_priority.lit
# Tests: cargo test --release --offline --lib closed_numeric_subterm_priority_tests
```

All three exact maintained files pass strict release gates and are executed by focused Rust tests. Fixed interval consumers retain actual written bound facts/citations across four literal negative-half-pi forms and two comparison directions. Strict/open contracts remain intact and premise permissions are inherited.

Numeric substitution now gives whole original scalar terms priority, then handles children and newly formed parents in one structural pass. Its supported constructors are unchanged; inserted values are not traversed. The old exact single-key wrapper still matches original nodes only. Actual table permutations prove the result is independent of row order, with checked equality/order/eval consumers and unchanged residual permissions. No persistent owner, AST representation, global search stage or cache contract was edited.

32 focused tests (bounds5, numeric5, Detailed9, quotient5, reflections8), eight final strict files and two focused FAQ fences pass. Before and after-bound froze an intermittent true cosine-endpoint failure; final16 fresh Normal/Detailed processes all accept it. Actual source IDs, failure isolation and stored-forall reuse are audited in the machine manifest.

These gates refer to the exact 693-file final2 source/binary snapshot. During closure, unrelated shared work added ten compile_to_latex files and changed three entrypoints; all eight repair files and 57 protected files remain unchanged. The archive retains the tested source with every hash verified. It preserves the live shared edits and does not claim verification of the resulting 703-file combination.

The [full migration report](../../../../plan/迁移的plan/legacy-trig-order-nonzero-audit-2026-10-06.md) retains121 independent sources,76 mathematically valid old-positive accepts plus2 unsafe old accepts, explicit author routes and unresolved sign/first-quadrant WD/tangent-order candidates. It preserves two rejected faulty Have fixtures, the corrected witness/obtain Direct test, partial gates and complete raw proof evidence. An old opaque-expression-versus-zero numeric comparison is excluded, not ported.

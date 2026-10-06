# Fixed tangent/cotangent quotient identities (2026-10-06)

Task: the authorized legacy migration tail, preserving the current architecture and partial-operation domains. This acceptance concerns two fixed laws, rather than a general trigonometric expander.

```litex
# Before: legacy accepted; current equality search rejected.
# forall x R:
#     sin(x)!=0
#     cos(x)!=0
#     =>:
#         tan(x)*cot(x)=1
# Now: complete parent WD, then TanCotProduct.
forall x R:
    sin(x)!=0
    cos(x)!=0
    =>:
        tan(x)*cot(x)=1

# Before: legacy accepted; current equality search rejected.
# forall x R:
#     cos(x)!=0
#     =>:
#         1+tan(x)^2=1/cos(x)^2
# Now: complete parent WD, then TanSquareReciprocalCosine.
forall x R:
    cos(x)!=0
    =>:
        1+tan(x)^2=1/cos(x)^2
```

The active sources are maintained [product](../../equal/by_builtin_rule/tan_cot_product.lit) and [square](../../equal/by_builtin_rule/tan_square_reciprocal_cosine.lit) tracers, each passing a strict release file gate. Equality direction, factor/summand order and repeated-multiplication squares are checked. Missing guards, poles, negative right sides, different angles and complex arguments are executed rejection controls in `tests/unit/execute/trig_quotient_relations/tests.rs`.

Each law owns its distinct typed angle certificate. Their mathematics follows from quotient definitions and the unit-circle identity. The matcher performs structural comparison and no premise search; enclosing equality WD owns the real domain and actual sine/cosine nonzero certificates. Detailed output projects the angle and keeps that parent evidence; all ten language outputs execute the actual leaf.

In the final public Runtime lifecycle, real product guard IDs f463/f464 and square guard f315 occur in parent WD. Stored universals f466/f317 are subsequently cited by the whole-source replay. A false target before and after each success has empty stores/infers. No AST, Env, Runtime, search ceiling or default domain was changed.

The new five tests, nine Detailed contracts and three language contracts pass (17 distinct tests):

```text
cargo test --release --offline --lib trig_quotient_relations_tests
cargo test --release --offline --lib json_output::project_detailed_tests
cargo test --release --offline --lib json_output::rule_language_methods_tests
target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_rule/tan_cot_product.lit
target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_rule/tan_square_reciprocal_cosine.lit
```

Both maintained tracers are included and executed by the focused Rust test. The general examples collector remains a separately tracked REL02 migration gap; no empty Cargo collector filter was counted.

The focused FAQ fence also passes the repository Markdown extractor/runner helper and strict CLI. The [migration report](../../../../plan/迁移的plan/legacy-trig-principal-composition-audit-2026-10-06.md) preserves 64 paired sources, explicit inverse-sine authors, remaining equivalent-bound and compound-angle attempts, raw receipts and exact coverage boundaries. A failed intermediate quotient author remains recorded even when the original fixed-law goal now succeeds.

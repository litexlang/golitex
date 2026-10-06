# Tuple/cart source-only example migration — 2026-10-06

This batch changes Litex source, the example collector and migration records. It adds no Rust code,
primitive interface, trust or premise. The verifier was frozen from the existing
release executable, SHA256 `3c08b12e50ed4f2b4f39949a285d90a78e1164ef656dc94ee80cf5e7d5b218c3`.
Textbooks and their exclusive dependencies remain deferred.

The proof spine of coordinate addition is unchanged: select each coordinate,
unfold addition once, calculate both sums, and reconstruct the same ordered result.
The old source used literal indexing:

```text
have fn add2(u,v cart(R,R)) cart(R,R) = (u[1]+v[1],u[2]+v[2])
add2((1,2),(3,4)) = (4,6)
```

The migrated checked source names the original tuple values and keeps the literal
conclusion. The extra names are checked values, rather than assumptions:

```litex
# Add ordered coordinates, unfold once, and check the original literal result.
# Literal values receive local names; no premise or kernel capability is added.
# Gate: target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_strategy/add2_calculation_chain.lit
have fn add2(u,v cart(R,R)) cart(R,R) = (u(1)+v(1),u(2)+v(2))
have p cart(R,R) = (1,2)
have q cart(R,R) = (3,4)
p(1) = 1
p(2) = 2
q(1) = 3
q(2) = 4
add2(p,q) = (p(1)+q(1),p(2)+q(2))
p(1)+q(1) = 1+3
p(2)+q(2) = 2+4
release thm tuple_equal_from_coordinates((p(1)+q(1),p(2)+q(2)),(1+3,2+4))
(1+3,2+4) = (4,6)
add2(p,q) = (1+3,2+4) = (4,6)
add2((1,2),(3,4)) = add2(p,q) = (4,6)
```

The actual registered source is
[add2_calculation_chain.lit](../../equal/by_builtin_strategy/add2_calculation_chain.lit).
Its source-order sketch/commit frames and strict file receipt are in the
[source-owned journal](../../../../plan/迁移的plan/proof_journals/tuple-cart-source-only-migration-2026-10-06.json).

The current completed batch covers 21 standalone files with 202 top-level results,
three qualified/imported files with 25 results, and nine migrated rejection files.
Six additional qualified negative probes check wrong coordinates and values.
The original exact-domain controls also pass: 39 positive files, 72 negative files;
the function-space corpus has 58 accept cases and 27 reject cases, with matching
failure phases and empty failed publications. These collections are separate;
their counts are not added to claim repository-wide coverage.

Nested selection uses a checked name for the selected inner value and an explicit
value equality before its ordinary call. Direct literal heads and the original
chained-call spelling remain separate unsupported-boundary observations in the
journal. Coordinate eval requires the explicit checked value before evaluation;
the failed deletion probe is retained. The user retired dimension, shape and
construction-projection interfaces, so no size/range substitute was introduced.
The thirteen dedicated old-interface positive files have been removed, with
their source snapshots retained in the journal. Three were registered by the
Python Obj collector, which now records them as retired interfaces and still
runs all eight syntax-rejection fixtures. No direct Rust file-path registration
was found. The earlier phrase "13 Rust registrations" was incorrect: thirteen
was the source-file count. The inventory audit, ten Python boundary tests and
eight real rejection gates pass; these are not a whole-Rust or whole-corpus gate.

The geometry draft has 176 of 227 items accepted in source order. Its 41
definitions and 186 public theorem headers preserve all original domains,
conditions and conclusions except coordinate spelling. Thirteen proof bodies
use checked local names or explicit equality bridges; the thirteenth, the
vertical-angle proof, remains unverified. Its unchanged public statement is:

```text
thm vertical_angles_equal:
    ? forall a, b, c, d, o cart(R, R):
        a != b
        c != d
        $is_on_segment(o, a, b)
        a != o
        b != o
        $is_on_segment(o, c, d)
        c != o
        d != o
        =>:
            $are_angles_congruent(a, o, c, b, o, d)
```

Interactive verification of this original target timed out at 60 and 180
seconds. A whole-draft strict file run then reached the 1200-second process
limit without a result envelope. The cold run does not locate its own stopping
statement; the interactive evidence locates item 177. These are incomplete
verification results, not mathematical rejection controls. The complete draft,
proof attempts and timeout receipt are retained, and the canonical geometry
source is unchanged. All batch processes are closed. Promotion still requires
the complete coherent chain and actual file/module gates to pass.

# Showcase repair and acceptance — 2026-10-14

Status: **complete**. 76/76 current Litex files have passing final gates; 23 source files were repaired. Three comment-only files were deleted.

The original audit had 12 files with their own failures, 11 chapters blocked by the Mechanics citation, and 10 observations stopped at the scan’s 300-second limit. Unblocking the citation exposed further chapter errors; the long geometry and Analysis checks exposed additional proof steps. This report supersedes the original failure status without rewriting that dated scan.

## Primary geometry tracer

Before, `configuration_scalar_bridge_4` refolded a midpoint already supplied by the configuration. The retained theorem statement and scalar calculation now use the known predicate directly:

```litex
    by def $problem_4_configuration(side_b,side_c,t,a,b,c,m)
    $is_midpoint(m,b,c)
```

A bare known positive predicate exposes its stored clauses. `by def` instead requires its defining body to be proved again. The repair uses the appropriate operation at the known-predicate boundary; other `by def` steps that introduce proved predicates remain.

## Files repaired

### [showcases/2D_Geometry/IMO/problem_4/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_4/solution.lit:500)

Known midpoint was refolded with `by def`. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
$is_midpoint(m,b,c)
```

### [showcases/2D_Geometry/IMO/problem_7/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_7/solution.lit:734)

The predecessor used by induction needed an explicit natural carrier. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
release thm natural_predecessor_nonnegative_7(target)
target - 1 $in N
```

### [showcases/2D_Geometry/IMO/problem_17/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_17/solution.lit:3785)

Known internal tangency was unnecessarily refolded. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
$circles_internally_tangent(center_2, radius_2, center_gamma, radius_gamma)
```

### [showcases/2D_Geometry/IMO/problem_13/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_13/solution.lit:832)

Known parallelism was refolded in the library bridge. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
$is_parallel(a, b, d, c)
$is_parallel(a, d, b, c)
```

### [showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/main.lit:174)

Nested rectangle/parallel facts needed explicit use; line membership projected the wrong set builder. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
$is_rectangle(a, b, c, d)
release thm set_builder_member(p, {r cart(R,R): det(vec(a,r),vec(a,b))=0})
```

### [showcases/The-Mechanics-of-Litex-Proof/citation.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/citation.lit:70)

Bodyless case headers blocked all eleven chapters. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
case b != 0:
    b != 0
```

### [showcases/The-Mechanics-of-Litex-Proof/chapter02-proofs-with-structure.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter02-proofs-with-structure.lit:519)

A bounded enumeration had no proof body. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
k^2 < 2
```

### [showcases/The-Mechanics-of-Litex-Proof/chapter04-proofs-with-structure-ii.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter04-proofs-with-structure-ii.lit:86)

Bodyless case arms and an empty bounded proof needed explicit branch calculations. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
case c >= 1:
    c > 0
```

### [showcases/The-Mechanics-of-Litex-Proof/chapter05-logic.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter05-logic.lit:40)

Bodyless parity cases and finite checks needed concrete proof bodies. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
case $is_even(n):
    n % 2 = 0
```

### [showcases/The-Mechanics-of-Litex-Proof/chapter06-induction.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter06-induction.lit:278)

Empty claim, explicit recurrence domain, and missing nonnegative product premise. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
n >= 0
pascal(a, b) * factorial(a) >= 0
```

### [showcases/The-Mechanics-of-Litex-Proof/chapter07-number-theory.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter07-number-theory.lit:676)

Bodyless cases/enumeration and missing real/nonzero carrier before the square-log argument. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
2^(1/2) $in R
2^(1/2) != 0
```

### [showcases/The-Mechanics-of-Litex-Proof/chapter08-functions.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter08-functions.lit:1656)

Empty enumeration/claims and implicit natural coordinate facts. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
u(2) $in N
u(2) >= 0
```

### [showcases/The-Mechanics-of-Litex-Proof/chapter09-sets.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter09-sets.lit:918)

Bodyless cases/enumerations and missing set-builder carrier/condition projections. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
release thm set_builder_member(x, {n N: (n + 1) $in {0}})
x $in N
x >= 0
```

### [showcases/The-Mechanics-of-Litex-Proof/chapter10-relations.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter10-relations.lit:557)

Bodyless finite cases/claims and missing natural carrier before cancellation. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
q(2) $in N
q(2) >= 0
```

### [showcases/linear_algebra/linear_algebra.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/linear_algebra/linear_algebra.lit:455)

A three-valued partial sum used unsupported induction coverage; exhaustive cases preserve its values. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
case k = 0: (0, 0)
case k = 1: plane_smul(coefficients(1), vectors(1))
case k = 2: plane_add(plane_smul(coefficients(1), vectors(1)), plane_smul(coefficients(2), vectors(2)))
```

### [showcases/math_concepts_in_litex/2_sets_functions_and_relations_in_nutshell/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/2_sets_functions_and_relations_in_nutshell/main.lit:37)

Goal-only extension and empty finite proof blocks. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
by extension union(first_set, second_set) = {1, 2, 3, 4}
```

### [showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/main.lit:65)

Empty case claims and index arithmetic needed before factorial unfolding. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
(n - 1) - r = n - r - 1
(n - 1) - (r - 1) = n - r
```

### [showcases/math_concepts_in_litex/5_linear_algebra/main2.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/5_linear_algebra/main2.lit:42)

Nested vector-space laws needed explicit use before guarded operations. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
$has_vector_space_laws(K, V, scalar_one, scalar_add, scalar_mul, zero_V, add_V, smul_V)
```

### [showcases/math_concepts_in_litex/6_abstract_algebra/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/6_abstract_algebra/main.lit:272)

Nested ring and homomorphism assumptions needed explicit use. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
$is_ring_homomorphism(A, add_A, zero_A, neg_A, mul_A, one_A, B, add_B, zero_B, neg_B, mul_B, one_B, map)
```

### [showcases/math_concepts_in_litex/9_topology/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/9_topology/main.lit:363)

Pullback construction needed nested space laws and cover-member carrier facts. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
open_sets_Y $subset power_set(Y)
```

### [showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/main.lit:66)

Nested neutral-geometry laws and betweenness/congruence facts needed explicit use. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
$TarskiNeutralDimensionlessSetting(Point, Bet, Cong, lower_a, lower_b, lower_c)
```

### [showcases/math_concepts_in_litex/16_category_theory_in_set_theory/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/16_category_theory_in_set_theory/main.lit:111)

Naturality guards needed functor arrow closure visible before proof-body execution. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
F_arrow(typed_source, typed_target, typed_arrow) $in target_category.Hom(F_object(typed_source), F_object(typed_target))
```

### [showcases/analysis/finite_products.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/finite_products.lit:25)

Finite-sequence/function-space carriers and nested coordinate predicates needed explicit projections. passes final gate.

Accepted source excerpt (read in its original local scope):

```litex
chosen_left $in finite_seq(U, n)
$is_in_infinite_cartesian_product(closed_range(1, n), U, X, chosen_infinite)
```

## Mathematical contracts

All 528 original top-level named theorem goal blocks across the 23 repaired files are unchanged, ignoring blank and comment lines; the machine-readable contract audit records this comparison against the original Git revision. The geometric configurations are retained. Proof-only changes provide explicit projections, calculation steps and nonempty case/enumeration bodies. Three source-shape changes deserve separate mention:

- `two_term_partial_sum` keeps its signature and the same three values at indices 0, 1 and 2; exhaustive cases replace its unsupported induction coverage. A finite enumeration proves coverage.
- The local `d_bound` predicate states `n >= 0` before evaluating the partial function. This follows from its existing `n >= 4` condition.
- The natural-transformation predicate repeats the two functors’ arrow Hom closure clauses. Its unchanged `natural_transformation_from_naturality` constructor proves them from the original functor premises.

No trust, user axiom, mathematical premise or kernel change was introduced by this task. Analysis retains its four pre-existing user axioms and exported `choice_property` abstract predicate (Chapter 2 also has two local induction-demo signatures in discarded sketch scopes) and is checked in ordinary mode. Its three small examples also pass an isolated strict gate with their explicit `maps` dependency. The complete chapter gate is the acceptance gate for their final registration.

## Empty files and module entries

Deleted comment-only files:

- `showcases/analysis/Introduction.lit`.
- `showcases/analysis/chapter01-introduction.lit`.
- `showcases/The-Mechanics-of-Litex-Proof/introduction.lit`.

Their export entries and current documentation links were removed. Mechanics now has 12 exports: citation and Chapters 0–10. Analysis has eight executable chapter/appendix exports and three trailing small-example exports, preserving its chapter dependency order. Registering `maps` fixes the previously unmounted `maps::` references in `finite_products`.

## Timeout findings

The previous 300 seconds was the audit runner’s per-process deadline, not a Litex timeout or a reported proof error. A configured `-f` run validates all earlier exports; an unregistered sidecar validates the whole configured prefix first. Running every late Analysis target separately therefore repeated the expensive book prefix. Batch JSON is emitted after execution, so an empty output file during that work does not establish a hang.

Earlier uncapped observations (output timestamp estimates, with concurrency):

| Target | Outcome | Seconds |
| --- | --- | ---: |
| Geometry base library | success | 614.260 |
| Analysis original eight-export module | success, ordinary | 2137.654 |
| IMO 13 before repair | completed with rejections | 682.990 |
| IMO 13 after repair | success, strict | 656.020 |
| Coordinate geometry before repair | completed with four rejected top-level statements | 367.440 |
| Coordinate geometry after repair | success, strict | 354.331 |

The persistent IMO 13 Session recorded approximately 240.640 seconds for `geometric_cover_implies_normalized_cover_13` and 192.435 seconds for `normalized_cover_implies_geometric_cover_13`. These timings explain why that proof plus its preceding library exceeds 300 seconds; they are not isolated kernel benchmarks. The first eleven-export Analysis retry completed after approximately 1688 seconds with an import failure caused by the finite-product proofs; those source steps were then repaired and the full module was rerun.

## Final verification evidence

Executable snapshot SHA-256: `f0ef676f91282bc0ff5c23a41aa01d62f6e0b5e7e918d39d9e6f586ba2d3ce21`. The shared executable was externally rebuilt during this task, so final coverage uses this fixed task-owned snapshot. Source hashes and every gate command, exit status and JSON envelope are recorded in the [machine-readable report](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/verification_runs/2026-10-14-showcase-repair.json).

Acceptance requires exit 0, JSON `kind: run`, `run_result: success`, `session_terminated: false`, no termination, and unchanged source fingerprints. The JSON coverage maps each current file to its passing target or module gate. Registered prefixes are validated once at the last target; this avoids repeated chapter-prefix work without skipping exports.

Focused and final commands follow these forms:

```sh
target/release/litex -lang en -strict -f <showcase-file>
target/release/litex -lang en -strict -r showcases/The-Mechanics-of-Litex-Proof
target/release/litex -lang en -r showcases/analysis
```

Actual final commands use the pinned executable path recorded in the JSON. Persistent Session journals retain attempted source, raw verifier responses, accepted blocks and materialization evidence. Ordinary statement failures reuse the same process; only hard parser termination required restarting and replaying the accepted prefix. No Lean replay, Rust suite or release/package acceptance is claimed for these Litex source repairs.

Final full-module timing: Analysis took approximately 1621.868 seconds (27 minutes); Mechanics took approximately 33.604 seconds. The pinned sweep measured 356.971 seconds for the geometry base library and 673.453 seconds for IMO 13. These timings include concurrent work.

Current verification totals by collection:

| Collection | Files covered | Current files |
| --- | ---: | ---: |
| 2D_Geometry | 28 | 28 |
| The-Mechanics-of-Litex-Proof | 12 | 12 |
| Write_Mathematically_Correct_Code_With_Litex | 1 | 1 |
| analysis | 11 | 11 |
| imo_inequalities | 5 | 5 |
| linear_algebra | 1 | 1 |
| litex_to_lean_adapter | 1 | 1 |
| math_concepts_in_litex | 17 | 17 |

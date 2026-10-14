# Showcase execution audit — 2026-10-14

All 79 currently present `showcases/**/*.lit` files were attempted: **46 passed, 23 failed, 10 timed out**.
The failures include 11 targets blocked by an earlier configured file and 12 files with their own failure. 3 passed files contain comments only.

The initial inventory contained 90 files. External workspace changes removed 11 during execution: Mathematics-in-Litex (9), analysis_notes (1), and school-math (1). Ten deleted files already had run records; school-math disappeared before launch. Those records are retained as historical evidence and excluded from the current totals. All 79 retained files have run records; their source bytes, configurations and the executable are unchanged from the initial fingerprint. No deleted files were restored.

## Execution and provenance

- Build: `cargo build --release --locked` (exit 0); version: `Litex 1.0.7-beta`.
- Git HEAD: `c6d4560771be0cc7703c349bc3102ef9bec84178`.
- Executable SHA-256: `f98a3454895f291d8b75f39bced13a4c2b727c8d46e756399af8d102c8031a84`.
- Each command: `target/release/litex -lang en -f <path>` from the repository root, using the file's existing direct-parent configuration.
- Acceptance: process exit 0, parsed JSON `kind: run`, `run_result: success`, `session_terminated: false`, `termination: null`.
- Ordinary verification; `-strict` was not applied. Registered targets execute their ordered prefix. Unlisted sidecars execute after every configured export. Files without a direct-parent config run independently.
- 35 current configurations, 68 registered files and 11 unregistered files; four concurrent independent processes; 300 seconds maximum per file.
- Elapsed scan time: 1300.584 seconds. These timings include concurrency and registered-prefix work; they are not isolated proof benchmarks.
- Every retained Rust source, Cargo manifest/lockfile, showcase Litex file and showcase configuration was hashed before and after the scan. No retained-input or executable drift was observed. Deleted paths and their original hashes are preserved separately.
- No proof, kernel, configuration or assumption edits were made.

The first gate, `showcases/analysis_notes/analysis.lit`, passed before that source was externally removed. A current representative failure is `showcases/2D_Geometry/IMO/problem_4/solution.lit`, whose `by def $is_midpoint(m,b,c)` is rejected. The current Cargo `run_showcases` collector is not registered, as documented in `tests/README.md`; this audit used real CLI processes instead.

## Collection totals

| Collection | Passed | Failed | Timeout |
| --- | ---: | ---: | ---: |
| 2D_Geometry | 23 | 3 | 2 |
| The-Mechanics-of-Litex-Proof | 1 | 12 | 0 |
| Write_Mathematically_Correct_Code_With_Litex | 1 | 0 | 0 |
| analysis | 6 | 0 | 7 |
| imo_inequalities | 5 | 0 | 0 |
| linear_algebra | 0 | 1 | 0 |
| litex_to_lean_adapter | 1 | 0 | 0 |
| math_concepts_in_litex | 9 | 7 | 1 |

## Concrete failure evidence

These are observed rejections and parser errors, not established kernel defects. No repair or after-state was implemented or tested.

### [showcases/2D_Geometry/IMO/problem_4/solution.lit:499](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_4/solution.lit:499)

`configuration_scalar_bridge_4` is rejected at `proof_body` index 1 (`by_def`). Five top-level statements are rejected in this file; later theorem-lookup errors include dependency fallout. Expected: these proof steps establish the theorem without rejection. The precise cause of the first rejection remains unclassified.

```litex
    by def $problem_4_configuration(side_b,side_c,t,a,b,c,m)
    by def $is_midpoint(m,b,c)
```

### [showcases/2D_Geometry/IMO/problem_7/solution.lit:732](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_7/solution.lit:732)

`zero_variation_forces_equal_to_first` is rejected at `$equal_after(target - 1)` with `search_proof`. Three top-level statements are rejected; consumers cannot call the failed theorem. This search miss alone does not establish a kernel defect.

```litex
                    ? $equal_after(offset + 1)

    1 + (target - 1) = target
    1 + (target - 1) <= n
    $equal_after(target - 1)
    a(1) = a(1 + (target - 1))
    a(1) = a(target)
```

### [showcases/2D_Geometry/IMO/problem_17/solution.lit:3783](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_17/solution.lit:3783)

The final `problem_17` theorem is rejected at `proof_body` index 18: the first `by def $circles_internally_tangent(...)` shown below. This is the file's only top-level rejection.

```litex
    by def $circle_internally_tangent_to_semicircle(center_2, radius_2, center_gamma, radius_gamma, point_a, point_b, point_c)
    by def $circle_internally_tangent_to_semicircle(center_3, radius_3, center_gamma, radius_gamma, point_a, point_b, point_c)
    by def $circles_internally_tangent(center_2, radius_2, center_gamma, radius_gamma)
    by def $circles_internally_tangent(center_3, radius_3, center_gamma, radius_gamma)
```

### [showcases/The-Mechanics-of-Litex-Proof/citation.lit:64](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/citation.lit:64)

Hard termination: `parse_error: unexpected end of tokens at line 68`. The parser reports the first branch header shown below. Both case headers lack a colon. All eleven configured Chapters 0–10 stop at this citation file before reaching their target. The showcase README points to the separate local `scripts/The-Mechanics-of-Litex-Proof/textbook` workspace; that workspace was outside this showcase-path scan.

```litex
    claim:
        ? b != 0 or a != 0
        by cases:
            ? b != 0 or a != 0
            case a != 0
            case b != 0
```

### [showcases/linear_algebra/linear_algebra.lit:446](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/linear_algebra/linear_algebra.lit:446)

The induction-based function definition is rejected at `have_fn_induc / coverage`: `k = 0 or k >= 1` was not established. The next theorem then causes a hard parse termination at line 463: `undefined name two_term_partial_sum`. The missing-name error follows the rejected definition; it is not an independently missing source declaration.

```litex
have fn two_term_partial_sum(coefficients finite_seq(R, 2), vectors finite_seq(R × R, 2), k closed_range(0, 2)) R × R by induc k from 0:
    case k = 0: (0, 0)
    case k >= 1:
        case k = 1: plane_smul(coefficients(1), vectors(1))
        case k != 1: plane_add(plane_smul(coefficients(1), vectors(1)), plane_smul(coefficients(2), vectors(2)))
```

### [showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/main.lit:640](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/main.lit:640)

The first rejected theorem, `segment_congruence_addition`, fails in case branch 0 at `a2 = b2` (`search_proof`). Seven top-level statements are rejected in this file. The full diagnostics in the machine record preserve the remaining rejections rather than treating all seven as independent defects.

```litex
        case a = b:
            release thm segment_congruence_symmetric(Point, Bet, Cong, lower_a, lower_b, lower_c, a, b, a2, b2)
            $are_segments_congruent(Point, Cong, a2, b2, a, b)
            (a2, b2, a, b) = (a2, b2, a, a)
            (a2, b2, a, a) $in Cong
            a2 = b2
            (b, c, b2, c2) = (a, c, a2, c2)
```

### [showcases/math_concepts_in_litex/16_category_theory_in_set_theory/main.lit:362](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/16_category_theory_in_set_theory/main.lit:362)

`vertical_composite_component_is_natural` fails before its proof body, in `goal_well_defined`. The rejected requirement for the composition below is `F_arrow(chosen_source, chosen_target, chosen_arrow) $in target_category.Hom(F_object(chosen_source), F_object(chosen_target))`. Two top-level statements are rejected; this audit does not decide whether the fix belongs in proof authoring or kernel behavior.

```litex
            target_category.compose(F_object(chosen_source), F_object(chosen_target), H_object(chosen_target), F_arrow(chosen_source, chosen_target, chosen_arrow), target_category.compose(F_object(chosen_target), G_object(chosen_target), H_object(chosen_target), alpha(chosen_target), beta(chosen_target))) = target_category.compose(F_object(chosen_source), H_object(chosen_source), H_object(chosen_target), target_category.compose(F_object(chosen_source), G_object(chosen_source), H_object(chosen_source), alpha(chosen_source), beta(chosen_source)), H_arrow(chosen_source, chosen_target, chosen_arrow))
```

### [showcases/math_concepts_in_litex/2_sets_functions_and_relations_in_nutshell/main.lit:37](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/2_sets_functions_and_relations_in_nutshell/main.lit:37)

Hard parse termination at line 37: `by extension: expects a nonempty proof body`. Six earlier top-level statements were accepted; this goal-only proof block was not accepted.

```litex
    by extension:
        ? union(first_set, second_set) = {1, 2, 3, 4}
```

### [showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/main.lit:67](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/main.lit:67)

Hard parse termination at line 69: `unexpected end of tokens`. The first case header shown below lacks a colon. Nine preceding top-level statements were accepted.

```litex
        by cases:
            ? choose_fn(n, r) = pascal_entry(r, n - r)
            case r <= n
            case r > n:
                impossible r < n
```

### [showcases/math_concepts_in_litex/6_abstract_algebra/main.lit:357](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/6_abstract_algebra/main.lit:357)

The first rejected theorem, `ring_homomorphism_kernel_is_ideal`, fails in its addition-closure claim. The first two adjacent equalities in the chain succeed; the last equality `add_B(zero_B, zero_B) = zero_B` is rejected (`failed_index: 2`). Four top-level statements are rejected in the file.

```litex
    claim:
        ? forall kernel_x, kernel_y {candidate A: map(candidate) = zero_B}:
            add_A(kernel_x, kernel_y) $in {candidate A: map(candidate) = zero_B}
        map(add_A(kernel_x, kernel_y)) = add_B(map(kernel_x), map(kernel_y)) = add_B(zero_B, zero_B) = zero_B
        release thm set_builder_member(add_A(kernel_x, kernel_y), {candidate A: map(candidate) = zero_B})
        add_A(kernel_x, kernel_y) $in {candidate A: map(candidate) = zero_B}
```

### [showcases/math_concepts_in_litex/5_linear_algebra/main2.lit:69](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/5_linear_algebra/main2.lit:69)

The first rejected theorem, `setting_add_left_cancel`, fails at `obtain inverse_p from exist inverse_p V st {add_V(p, inverse_p) = zero_V}` (`obtain_obj_from_exist_fact`). Six top-level statements are rejected in this second export; its preceding `main.lit` passes.

```litex
        =>:
            q = r
    obtain inverse_p from exist inverse_p V st {add_V(p, inverse_p) = zero_V}
    add_V(inverse_p, p) = add_V(p, inverse_p) = zero_V
    q = add_V(zero_V, q) = add_V(add_V(inverse_p, p), q) = add_V(inverse_p, add_V(p, q)) = add_V(inverse_p, add_V(p, r)) = add_V(add_V(inverse_p, p), r) = add_V(zero_V, r) = r
```

### [showcases/math_concepts_in_litex/9_topology/main.lit:359](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/9_topology/main.lit:359)

The only rejected theorem, `continuous_image_of_compact_is_compact`, fails while checking the `pullback_cover` function body. Its inverse-image template requires `cover(index) $in power_set(Y)`, which was not established during this well-definedness check.

```litex
            =>:
                exist J power_set(Index) st {$is_finite_set(J), fn_range(\restricted<X,Y,f,K>) $subset family_union(fn_range(\restricted<Index,open_sets_Y,cover,J>))}
        have fn pullback_cover(index Index) open_sets_X = \inverse_image<X,Y,f,cover(index)>
```

## Timeouts and coverage limits

- `showcases/2D_Geometry/IMO/problem_13/solution.lit`: killed after 300.017 seconds; no successful completion was observed. This is an unconfirmed result, not a proof rejection. A configured-prefix timeout does not show that the requested target was reached.
- `showcases/2D_Geometry/geo.lit`: killed after 300.043 seconds; no successful completion was observed. This is an unconfirmed result, not a proof rejection. A configured-prefix timeout does not show that the requested target was reached.
- `showcases/analysis/appendix-a-logic-and-proof-language.lit`: killed after 300.007 seconds; no successful completion was observed. This is an unconfirmed result, not a proof rejection. A configured-prefix timeout does not show that the requested target was reached.
- `showcases/analysis/chapter06-sequential-limits.lit`: killed after 300.012 seconds; no successful completion was observed. This is an unconfirmed result, not a proof rejection. A configured-prefix timeout does not show that the requested target was reached.
- `showcases/analysis/chapter07-series.lit`: killed after 300.012 seconds; no successful completion was observed. This is an unconfirmed result, not a proof rejection. A configured-prefix timeout does not show that the requested target was reached.
- `showcases/analysis/chapter08-infinite-sets.lit`: killed after 300.017 seconds; no successful completion was observed. This is an unconfirmed result, not a proof rejection. A configured-prefix timeout does not show that the requested target was reached.
- `showcases/analysis/finite_products.lit`: killed after 300.012 seconds; no successful completion was observed. This is an unconfirmed result, not a proof rejection. A configured-prefix timeout does not show that the requested target was reached.
- `showcases/analysis/maps.lit`: killed after 300.019 seconds; no successful completion was observed. This is an unconfirmed result, not a proof rejection. A configured-prefix timeout does not show that the requested target was reached.
- `showcases/analysis/naturals.lit`: killed after 300.011 seconds; no successful completion was observed. This is an unconfirmed result, not a proof rejection. A configured-prefix timeout does not show that the requested target was reached.
- `showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/main.lit`: killed after 300.054 seconds; no successful completion was observed. This is an unconfirmed result, not a proof rejection. A configured-prefix timeout does not show that the requested target was reached.

The historical original Analysis gate in `showcases/analysis/verification.json` records 1611.946 seconds for an earlier source/binary input. This is evidence that a 300-second cutoff may be too short, not verification of the current snapshot.

The Analysis source has four explicit user axioms (two each in Chapter 5 and Chapter 8). Ordinary execution permits them; a passing result does not certify absence of assumptions. No strict or Lean-kernel verification claim is made.

Passed files containing no executable statements:

- `showcases/The-Mechanics-of-Litex-Proof/introduction.lit`
- `showcases/analysis/Introduction.lit`
- `showcases/analysis/chapter01-introduction.lit`

The draft `math_concepts_in_litex/17_probability_theory` has no active `.lit` entry and contributes no executable file. The five executable IMO inequality proofs all pass. This scan excludes Markdown fences, Lean compilation, executable extraction, other repository examples and local textbook workspaces.

## Per-file results

| File | Result | Seconds | Target statements accepted / rejected |
| --- | --- | ---: | ---: |
| [showcases/2D_Geometry/IMO/problem_1/Solution-1/geo_definitions.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_1/Solution-1/geo_definitions.lit) | pass | 0.514 | 40 / 0 |
| [showcases/2D_Geometry/IMO/problem_1/Solution-1/predicate.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_1/Solution-1/predicate.lit) | pass | 0.943 | 7 / 0 |
| [showcases/2D_Geometry/IMO/problem_1/Solution-1/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_1/Solution-1/solution.lit) | pass | 34.543 | 5 / 0 |
| [showcases/2D_Geometry/IMO/problem_1/Solution-1/theorem.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_1/Solution-1/theorem.lit) | pass | 12.726 | 10 / 0 |
| [showcases/2D_Geometry/IMO/problem_1/Solution-2/geo_definitions.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_1/Solution-2/geo_definitions.lit) | pass | 0.510 | 40 / 0 |
| [showcases/2D_Geometry/IMO/problem_1/Solution-2/predicate.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_1/Solution-2/predicate.lit) | pass | 0.989 | 7 / 0 |
| [showcases/2D_Geometry/IMO/problem_1/Solution-2/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_1/Solution-2/solution.lit) | pass | 66.841 | 5 / 0 |
| [showcases/2D_Geometry/IMO/problem_1/Solution-2/theorem.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_1/Solution-2/theorem.lit) | pass | 8.105 | 11 / 0 |
| [showcases/2D_Geometry/IMO/problem_12/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_12/solution.lit) | pass | 35.061 | 14 / 0 |
| [showcases/2D_Geometry/IMO/problem_13/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_13/solution.lit) | timeout | 300.017 | — |
| [showcases/2D_Geometry/IMO/problem_15/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_15/solution.lit) | pass | 8.107 | 7 / 0 |
| [showcases/2D_Geometry/IMO/problem_17/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_17/solution.lit) | fail | 170.810 | 102 / 1 |
| [showcases/2D_Geometry/IMO/problem_18/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_18/solution.lit) | pass | 72.082 | 28 / 0 |
| [showcases/2D_Geometry/IMO/problem_2/Solution-1/predicate.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_2/Solution-1/predicate.lit) | pass | 0.036 | 1 / 0 |
| [showcases/2D_Geometry/IMO/problem_2/Solution-1/solution_part_a.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_2/Solution-1/solution_part_a.lit) | pass | 0.929 | 1 / 0 |
| [showcases/2D_Geometry/IMO/problem_2/Solution-1/solution_part_b.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_2/Solution-1/solution_part_b.lit) | pass | 0.935 | 6 / 0 |
| [showcases/2D_Geometry/IMO/problem_2/Solution-1/theorem.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_2/Solution-1/theorem.lit) | pass | 0.669 | 4 / 0 |
| [showcases/2D_Geometry/IMO/problem_2/Solution-2/predicate.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_2/Solution-2/predicate.lit) | pass | 0.010 | 1 / 0 |
| [showcases/2D_Geometry/IMO/problem_2/Solution-2/solution_part_a.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_2/Solution-2/solution_part_a.lit) | pass | 1.311 | 1 / 0 |
| [showcases/2D_Geometry/IMO/problem_2/Solution-2/theorem.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_2/Solution-2/theorem.lit) | pass | 1.264 | 3 / 0 |
| [showcases/2D_Geometry/IMO/problem_20/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_20/solution.lit) | pass | 99.076 | 82 / 0 |
| [showcases/2D_Geometry/IMO/problem_3/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_3/solution.lit) | pass | 6.664 | 17 / 0 |
| [showcases/2D_Geometry/IMO/problem_4/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_4/solution.lit) | fail | 22.107 | 29 / 5 |
| [showcases/2D_Geometry/IMO/problem_5/Solution-1/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_5/Solution-1/solution.lit) | pass | 3.856 | 5 / 0 |
| [showcases/2D_Geometry/IMO/problem_5/Solution-2/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_5/Solution-2/solution.lit) | pass | 30.761 | 36 / 0 |
| [showcases/2D_Geometry/IMO/problem_7/solution.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/IMO/problem_7/solution.lit) | fail | 10.292 | 26 / 3 |
| [showcases/2D_Geometry/geo.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/geo.lit) | timeout | 300.043 | — |
| [showcases/2D_Geometry/geo_definitions.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/2D_Geometry/geo_definitions.lit) | pass | 0.565 | 40 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter00-introduction.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter00-introduction.lit) | dependency_blocked | 0.041 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter01-proofs-by-calculation.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter01-proofs-by-calculation.lit) | dependency_blocked | 0.041 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter02-proofs-with-structure.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter02-proofs-with-structure.lit) | dependency_blocked | 0.040 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter03-parity-and-divisibility.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter03-parity-and-divisibility.lit) | dependency_blocked | 0.040 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter04-proofs-with-structure-ii.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter04-proofs-with-structure-ii.lit) | dependency_blocked | 0.039 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter05-logic.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter05-logic.lit) | dependency_blocked | 0.039 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter06-induction.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter06-induction.lit) | dependency_blocked | 0.040 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter07-number-theory.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter07-number-theory.lit) | dependency_blocked | 0.040 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter08-functions.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter08-functions.lit) | dependency_blocked | 0.041 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter09-sets.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter09-sets.lit) | dependency_blocked | 0.040 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/chapter10-relations.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/chapter10-relations.lit) | dependency_blocked | 0.037 | 0 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/citation.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/citation.lit) | fail | 0.040 | 5 / 0 |
| [showcases/The-Mechanics-of-Litex-Proof/introduction.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/The-Mechanics-of-Litex-Proof/introduction.lit) | pass | 0.005 | 0 / 0 |
| [showcases/Write_Mathematically_Correct_Code_With_Litex/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/Write_Mathematically_Correct_Code_With_Litex/main.lit) | pass | 0.077 | 26 / 0 |
| [showcases/analysis/Introduction.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/Introduction.lit) | pass | 0.005 | 0 / 0 |
| [showcases/analysis/appendix-a-logic-and-proof-language.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/appendix-a-logic-and-proof-language.lit) | timeout | 300.007 | — |
| [showcases/analysis/chapter01-introduction.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/chapter01-introduction.lit) | pass | 0.006 | 0 / 0 |
| [showcases/analysis/chapter02-natural-numbers.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/chapter02-natural-numbers.lit) | pass | 0.351 | 55 / 0 |
| [showcases/analysis/chapter03-set-theory.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/chapter03-set-theory.lit) | pass | 2.086 | 110 / 0 |
| [showcases/analysis/chapter04-integers-and-rationals.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/chapter04-integers-and-rationals.lit) | pass | 24.945 | 145 / 0 |
| [showcases/analysis/chapter05-real-numbers.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/chapter05-real-numbers.lit) | pass | 234.241 | 268 / 0 |
| [showcases/analysis/chapter06-sequential-limits.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/chapter06-sequential-limits.lit) | timeout | 300.012 | — |
| [showcases/analysis/chapter07-series.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/chapter07-series.lit) | timeout | 300.012 | — |
| [showcases/analysis/chapter08-infinite-sets.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/chapter08-infinite-sets.lit) | timeout | 300.017 | — |
| [showcases/analysis/finite_products.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/finite_products.lit) | timeout | 300.012 | — |
| [showcases/analysis/maps.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/maps.lit) | timeout | 300.019 | — |
| [showcases/analysis/naturals.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/analysis/naturals.lit) | timeout | 300.011 | — |
| [showcases/imo_inequalities/imo_1983_p6.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/imo_inequalities/imo_1983_p6.lit) | pass | 3.676 | 9 / 0 |
| [showcases/imo_inequalities/imo_1995_p2.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/imo_inequalities/imo_1995_p2.lit) | pass | 4.097 | 4 / 0 |
| [showcases/imo_inequalities/imo_2001_p2.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/imo_inequalities/imo_2001_p2.lit) | pass | 7.578 | 8 / 0 |
| [showcases/imo_inequalities/imo_2005_p3.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/imo_inequalities/imo_2005_p3.lit) | pass | 2.836 | 4 / 0 |
| [showcases/imo_inequalities/imo_2006_p3.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/imo_inequalities/imo_2006_p3.lit) | pass | 7.626 | 7 / 0 |
| [showcases/linear_algebra/linear_algebra.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/linear_algebra/linear_algebra.lit) | fail | 6.128 | 56 / 1 |
| [showcases/litex_to_lean_adapter/source.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/litex_to_lean_adapter/source.lit) | pass | 0.010 | 1 / 0 |
| [showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit) | pass | 0.391 | 10 / 0 |
| [showcases/math_concepts_in_litex/11_multivariable_calculus_in_nutshell/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/11_multivariable_calculus_in_nutshell/main.lit) | pass | 2.227 | 16 / 0 |
| [showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell/main.lit) | pass | 1.691 | 21 / 0 |
| [showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit) | pass | 4.056 | 30 / 0 |
| [showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/main.lit) | fail | 0.453 | 86 / 7 |
| [showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/main.lit) | timeout | 300.054 | — |
| [showcases/math_concepts_in_litex/16_category_theory_in_set_theory/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/16_category_theory_in_set_theory/main.lit) | fail | 4.427 | 47 / 2 |
| [showcases/math_concepts_in_litex/2_euclidean_geometry/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/2_euclidean_geometry/main.lit) | pass | 39.378 | 27 / 0 |
| [showcases/math_concepts_in_litex/2_sets_functions_and_relations_in_nutshell/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/2_sets_functions_and_relations_in_nutshell/main.lit) | fail | 0.006 | 6 / 0 |
| [showcases/math_concepts_in_litex/3_number_theory/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/3_number_theory/main.lit) | pass | 0.137 | 26 / 0 |
| [showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/main.lit) | fail | 0.316 | 9 / 0 |
| [showcases/math_concepts_in_litex/5_linear_algebra/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/5_linear_algebra/main.lit) | pass | 4.053 | 56 / 0 |
| [showcases/math_concepts_in_litex/5_linear_algebra/main2.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/5_linear_algebra/main2.lit) | fail | 5.718 | 23 / 6 |
| [showcases/math_concepts_in_litex/6_abstract_algebra/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/6_abstract_algebra/main.lit) | fail | 0.741 | 35 / 4 |
| [showcases/math_concepts_in_litex/7_calculus/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/7_calculus/main.lit) | pass | 0.899 | 17 / 0 |
| [showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/main.lit) | pass | 25.632 | 45 / 0 |
| [showcases/math_concepts_in_litex/9_topology/main.lit](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/math_concepts_in_litex/9_topology/main.lit) | fail | 0.144 | 25 / 1 |

Statement counts describe the target JSON entries, not all statements in its configured prefix. A blocked target has no target statement results.

## Retained evidence

- [Machine-readable results, diagnostics and before/after fingerprints](/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/verification_runs/2026-10-14-showcase-check.json).
- Raw stdout/stderr, task runner and scan metadata remain in `/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-14/showcase-check` (ignored task draft area). Each machine-readable result names its exact raw-output path.
- Mathematical source and configurations remain unchanged. No open failure is marked repaired by this audit.

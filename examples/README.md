# Litex Examples

Mathematical examples and the phase-oriented acceptance tree for the current
Litex pipeline (`src/`).

[Definitions and proofs](proof_search/README.md) pairs an offline interactive
diagram with editable journal-style figures: a checked object declaration builds
the context, then staged proof search uses it to verify a new fact.

[From checked evidence to Lean](lean_compilation/README.md) follows a real
Detailed evidence tree into generated Lean and explains the semantic definitions
and proved bridges supplied by `Litex.lean`, with an interactive view and figures.

[Collected IMO proofs](imo/README.md) brings together inequalities, geometry,
functional equations and the existing miniF2F IMO proof variants.

> **When extending or repairing an example, use one `-session` and keep its
> accepted context after an ordinary failure. Do not rerun the whole file after
> every few new lines.** The [Agent Guide](../docs/AgentGuide.md) shows a short
> comparison and the restart/replay boundaries. Clean file commands below are
> baseline, checkpoint, and final acceptance gates.

## Layout

```text
examples/
  imo/                 collected IMO problems, solutions and verification status
  proof_nodes/          verify / searched_proof tracers
  proof_search/         interactive proof-search explanation and static figures
  lean_compilation/     evidence replay into Lean and the role of Litex.lean
  stmt_nodes/           exec_stmt arms
  wd/  wd_negative/     well-definedness positives / must-fail
  equal_negative/       equality must-fail probes
  infer/                store → Infer*Result consequences
  tokenize/             tokenizer / Unicode input surface
  module_manager/       -r / -f / litex.config mount
  real_analysis/series/ imported real series source library and rejection controls
  number_theory/congruences/ imported integer congruence library and rejection controls
  topology/foundations/ imported topology, continuous maps and connectedness
  topology/separation_compactness/ separation axioms and general finite-subcover compactness
  agent_session_demo/    Python driver for persistent-Session authoring
  knowledge_base/       persist / restore goldens
  litex_vs_lean_speed/  Litex / Lean checking-time comparisons and harness
  _internal/            fixtures / drafts / non-public regressions
  *.lit                focused standalone regressions
```

## Acceptance

```bash
target/release/litex -f examples/knowledge_base/def_prop/is_pos.lit
target/release/litex -f <any-file-under-phase-dirs>
```

Exit 0 (or intentional non-zero for `wd_negative` / `equal_negative`) is the gate.
Each subdirectory README has a `find … | sort` run-all snippet.

One user-visible kernel stage → one subdirectory. Prefer a **new** `.lit` for a
new/widened rule; use a descriptive filename in the matching phase directory.

Finite-set inclusion tracers:

- [A subset of a finite set is finite](proof_nodes/atomic/by_builtin_strategy/subset_of_finite_set.lit).
- [Subset size comparison using finiteness proved by WD](proof_nodes/atomic/by_builtin_rule/less_equal_finite_set_size_subset_wd.lit).
- [A finite subset of equal size equals its containing set](proof_nodes/equal/by_builtin_rule/finite_set_equal_from_subset_size.lit), including an explicit singleton proof.
- [A proper finite subset has smaller size](proof_nodes/atomic/by_builtin_rule/less_finite_set_size_proper_subset.lit), using either `$proper_subset` or `$subset` with disequality.

Checked function-return order formation: [positive tracer](wd/checked_function_order_domain.lit)
and negative controls for [invalid index](wd_negative/checked_function_order_invalid_index.lit),
[missing guard](wd_negative/checked_function_order_unproved_guard.lit),
[complex return](wd_negative/checked_function_order_complex.lit),
[false order](wd_negative/checked_function_order_false.lit) and
[an alternative guarded signature](wd_negative/checked_function_order_alternative_guard.lit).

Real sequence limit tracers:

- [Explicit epsilon-N proof for 1/k, then selected-value use](wd/sequence_limit.lit).
- [Equivalent seq(R) / fn(k N+) R and finite-existence interfaces](wd/sequence_limit_interfaces.lit).
- [Common sequence-limit proofs](wd/sequence_limit_common_proofs.lit): explicit `1/n -> 0`, rational examples, `sin(n)/n -> 0`, `sqrt(1+1/n) -> 1`, and `(1/2)^n -> 0`; also finite initial changes, even-index subsequences, eventual positivity/nonzero terms, and divergence of `n`. Each convergence proof precedes `lim` use.
- One `seq_limit_*.lit` example per theorem in `stmt_nodes/release_and_expand/builtin_thm/`.

The [Riemann integral absolute-bound example](real_analysis/integral_absolute_bound/README.md)
checks positive and reversed orientations, equal endpoints and exact domains.

Ordered real series:

- [Imported library example](real_analysis/series/README.md): partial sums,
  candidate/convergence properties, guarded selected values, linearity, tails,
  finite support and finite-prefix corrections. The geometric sum is proved
  before it is selected; eight independent controls check nearby invalid uses.

Ordered finite real derivatives:

- [Ordered vector-coordinate partials](real_analysis/multivariable/higher_order/README.md):
  zero order, explicit third-order polynomial profiles, equivalent complete
  function paths, actual restricted domains and native first/second bridges.
- [Unary real higher derivatives](real_analysis/higher_derivatives/README.md):
  a separate real-input selector, zero/first/third orders and candidate-first
  selection. Both suites have installed-layout refusal and Session liveness controls.

- [Higher derivative source laws](real_analysis/higher_derivative_laws/README.md):
  candidate-first finite-order linearity for independent unary profiles and
  ordered vector-coordinate paths, with installed refusal/liveness controls.
- [Finite regularity and smoothness](real_analysis/regularity/README.md):
  actual-open-domain C^k, unary/vector constant smoothness and a C^2 mixed-partial
  exchange example, preserving explicit candidates before numerical selection.

- [Regularity source laws](real_analysis/regularity_laws/README.md): explicit
  C^k and smoothness closure through imported definitions and named proofs.
- [Finite unary function sums](real_analysis/function_sums/README.md) and
  [one-vector function sums](real_analysis/multivariable/function_sums/README.md):
  exact domains, used-prefix derivative candidates, empty sums and continuity.
- [Real restriction of the Jacobian counterexample](real_analysis/jacobian_counterexample/README.md):
  nine proved partials, actual Jacobian determinant -2 everywhere, explicit
  collisions and no left inverse. The original complex theorem is outside this example.

Real three-dimensional cross products:

- [Imported cross-product example](real_analysis/multivariable/cross_product/README.md):
  right-handed basis products, exact finite-function inputs, bilinearity,
  perpendicularity, Lagrange/norm-square and triple-product laws, with nine
  rejection controls and persistent-Session liveness after rejection.

Elementary number theory:

- [Imported congruences](number_theory/congruences/README.md): native divisibility,
  equivalence and arithmetic laws, remainder reduction, positive divisor moduli,
  generic callers and controls for invalid domains and cancellation.

General topology:

- [Imported foundations](topology/foundations/README.md): arbitrary and empty
  spaces, continuity and closed preimages, homeomorphisms, connectedness and
  clopen sets, with independent contracts and missing-premise controls.
- [Separation and compactness](topology/separation_compactness/README.md):
  T0/T1/Hausdorff, compact finite subsets and continuous images, infinite
  compact/noncompact examples, exact restriction domains and their controls.

Finite-point real function limit tracers:

- [Explicit punctured epsilon-delta proof, then selected-value use](wd/real_function_limit_at.lit): `x^2/x` at zero without calling the function at zero.
- [Polynomial and rational limit proofs](wd/real_function_limit_common_proofs.lit), [relative endpoint](wd/real_function_limit_endpoints.lit), and [existence/congruence interfaces](wd/real_function_limit_interfaces.lit).
- One `fn_limit_at_*.lit` example per theorem in `stmt_nodes/release_and_expand/builtin_thm/` and `real_function_limit_*.lit` rejection controls in `wd_negative/`.

Left/right function limit tracers:

- [Jump: left -1, right 1 and no ordinary candidate](wd/real_function_limit_sides.lit), with explicit directional epsilon-delta proofs.
- [Matching sides for x²](wd/real_function_limit_sides_agree.lit), [R+ endpoint and absent left side](wd/real_function_limit_sides_endpoint.lit), and [direction-preserving interfaces](wd/real_function_limit_sides_interfaces.lit).
- Directional theorem and bridge examples are in `stmt_nodes/release_and_expand/builtin_thm/`; rejection controls are in `wd_negative/real_function_limit_sides_*.lit`.

## Other

- [Python Session agent loop](agent_session_demo/README.md) drives the real CLI,
  checks recovery after a rejected statement, and compares dependent-prefix
  verification counts.
- `_internal/` is developer material (including larger case-study regressions),
  not the public reading path.
- Earlier Litex-to-Lean pairs are archived locally under
  `scripts/legacy_to_lean/lean/examples/`, which is excluded from Git.

Standalone regression examples:

- [A shallow embedding of higher-order logic](hol_embedding.lit), provided by chegnxuan huang: Boolean-valued predicates and quantifiers, interpretations of the HOL Light axioms, and constructed natural numbers with addition.
- [Claim/obtain scope](claim_obtain_scope.lit).
- [Nonempty-set property arguments](nonempty_set_property_arguments.lit).
- [Function construction by unique existence](have_fn_by_unique_existence.lit).
- [Object-definition equalities](object_definition_equalities.lit).
- [Template-defined type interfaces](stmt_nodes/definition/template_type_interfaces.lit).
- [Inverse trigonometric principal intervals](inverse_trig_principal_intervals.lit).

- [Euclidean gcd transformations and supplied modular inverses](number_theory/euclidean_inverses/README.md): strict generic/source callers, guarded cancellation, linear congruences,20 semantic controls and installed std imports.

- [Finite maps and counting](combinatorics/finite_maps/README.md): pigeonhole witnesses, equal-size bijection criteria, empty sets, independent contracts and installed std imports.
- [Finite-set inclusion-exclusion](combinatorics/finite_sets/README.md): overlapping unions, symmetric differences, products, powersets, empty boundaries and explicit imported finiteness evidence.
- [Natural binomial coefficients](combinatorics/binomial/README.md): Pascal recursion, symmetry, column formulas, positivity, row order and full natural-domain boundaries.

- [Group maps and subgroup transport](algebra/group_maps/README.md): native composition, image/preimage subgroups, normal inverse images and noncommutative/trivial groups.
- [Normal subgroup images and composition kernels](algebra/normal_images/README.md): ambient surjectivity, actual restricted images and a kernel identity valid for complete maps without a homomorphism premise.
- [Group inverse laws](algebra/inverse_laws/README.md): inverse products and right equations, including order-sensitive noncommutative examples.
- [Field zero and cancellation laws](algebra/field_zero_laws/README.md): zero absorption, nonzero cancellation and zero-product boundaries.
- [Field additive laws](algebra/field_additive_laws/README.md): additive identity, inverses, cancellation and double negation.
- [Field negation laws](algebra/field_negation_laws/README.md): negation of sums and products, including zero operands.
- [Field inverse laws](algebra/field_inverse_laws/README.md): guarded inverse, inverse of a product and zero-input boundaries.
- [Field difference laws](algebra/field_difference_laws/README.md): distributivity, multiplication over differences and the zero-difference criterion.
- [Field linear equations](algebra/field_linear_equations/README.md): unique linear and affine solutions with nonzero coefficients.
- [Zero-coefficient field equations](algebra/field_zero_equations/README.md): all-solution, no-solution and distinct-witness cases.
- [Two-element field](algebra/two_element_field/README.md): a checked characteristic-two instance and cross-file use of the generic field laws.
- [Vector space over the two-element field](algebra/two_element_vector_space/README.md): maps, kernels, a basis, dimension one and rank-nullity.
- [Zero products in a field](algebra/field_zero_product/README.md): the zero-product characterization over real and two-element fields.
- [Group conjugation](algebra/conjugation_laws/README.md): product preservation, bijectivity and the connection with commutation.
- [Elementary group identities](algebra/group_elementary_laws/README.md): right identities, idempotents and a nonidentity self-inverse element.
- [Powers and integer congruence](number_theory/congruence_powers/README.md): natural powers, remainder reduction and supplied modular inverses.

- [Finite event probability](probability/finite_events/README.md): generic event, conditional/Bayes and independence contracts, actual uniform/Dirac probability spaces and guarded boundaries.
- [Finite pushforward probability](probability/pushforward/README.md): actual image distributions, dice parity, constant maps and retained zero-mass image points.

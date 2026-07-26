# Analysis II translation blockers

## Task context

- Task: Plan and implement Tao's *Analysis II* as a Litex textbook project.
- Scope: The source in `scripts/Analysis2/Analysis II.txt`, structured
  translation records, and the final textbook module.
- Related workspace: `scripts/Analysis2/` and `textbooks/Analysis2/`.

Add an item here only after a direct Litex attempt. Every item must include the
attempted statement or minimal Litex example, the exact verifier behavior when
available, the desired interface, a root-cause class, and the primary Litex
label `trust` or `kernel_problem`.

## do_not_know_how_to_formalize

- **Chapter 1 source proofs remain explicit proof debt.**
  Attempt: all 32 named items were translated in
  `scripts/textbooks_drafts/Analysis2/chapter01-metric-spaces.lit`, and the definitions plus
  representative use probes were run in the real caller context. Exact
  command:
  `target/release/litex -compact -f
  scripts/textbooks_drafts/Analysis2/chapter01-metric-spaces.lit`.
  Result: verifier `"result": "success"`, with 28 explicit `trust`
  statements. Desired state: replace each source-local theorem trust with a
  checked proof while preserving the current declaration shapes. Root cause:
  omitted exercise proofs, finite choice constructions, finite-dimensional
  norm estimates, and the source's compact open-cover argument have not yet
  been formalized. Primary label: `trust`.

- **Arbitrary-union openness stops at the source-local subset bridge.**
  Attempt: a persistent release `try:` session verified both directions of the
  template-membership bridge for `set_family_union`: first write
  `\\set_family_union<X,A,family> = {x X:
  $is_in_set_family_union(X,A,family,x)}`, then unfold the predicate and
  introduce or eliminate its existential index witness. The full direct proof
  of `arbitrary_union_of_metric_open_sets_is_open` then repeatedly ended with
  an unlocated `ExecStmtError` when a locally proved
  `forall x family(alpha): x $in \\set_family_union<X,A,family>` was lifted to
  `family(alpha) $subset \\set_family_union<X,A,family>`, or when that bridge
  was embedded in the final `by extension` proof. Desired interface: a
  diagnosable way to discharge subset introduction from a local pointwise
  proof, or an existing named subset-introduction theorem usable in this
  context. Root cause is not yet isolated beyond this proof/diagnostic gap.
  Primary label: `trust`.

- **Arbitrary closed intersections stop at the adherence-transfer bridge.**
  Attempt: a persistent release `try:` session checked the elementary fact
  that a ball disjoint from `family(alpha)` is disjoint from the family
  intersection. In the real source theorem, however, the next step—using
  that empty intersection against adherence of the family intersection—ends
  at `by contra: failed to execute proof`, even after spelling out the family
  intersection as its set-builder form. Desired interface: stable unfolding
  and instantiation of an adherence predicate whose set argument is a
  template result, or a diagnosable bridge for that direct pointwise step.
  This is recorded as a formulation/diagnostic gap, not yet a confirmed
  kernel defect. Primary label: `trust`.

- **Metric-ball nesting also stops at the pointwise-to-subset bridge.**
  Attempt: an outermost release `try:` verified the triangle estimate
  `d(z,c) < r` from `d(z,y) < s` and `s + d(y,c) = r`, and the new named
  ball membership bridges verify both conversions between this inequality and
  ball membership. The intended final statement
  `metric_ball(y,s) $subset metric_ball(c,r)` still ends in an unlocated
  `ExecStmtError` when lifting the checked pointwise implication to `$subset`.
  Desired interface: a diagnosable, stable subset-introduction rule for a
  proved universal membership fact. Root cause overlaps the arbitrary-union
  subset bridge gap but is not yet isolated as a verifier defect. Primary
  label: `trust`.

- **Analysis I reuse is not yet a stable cross-book dependency.**
  Attempt: Chapter 1 was modeled as its own project and the real convergence
  and finite-dimensional Heine--Borel statements were written against local
  source-facing relations. There is no configured canonical project import
  that exposes Analysis I without coupling this book to another textbook
  namespace. Desired interface: a reusable standard-library convergence and
  finite-dimensional compactness layer, or an explicit supported cross-book
  dependency. Root cause: library organization rather than a verifier defect.
  Primary label: `trust`.

## strange_behavior_of_litex

- **A parse failure inside outermost `try:` stops a `-session -before`
  session.** Minimal attempted frame:

  ```litex
  try:
      prop has_metric_open_neighborhood_form_at(...):
          forall V power_set(Y):
              ...
              =>:
                  exist U power_set(X) st {
                      ...,
                      forall x U:
                          f(x) $in V
                  }
  ```

  Exact behavior: frame `def214b` returned
  `ParseError: unexpected indent at line 8`; the next valid outermost-`try:`
  frame returned `{"event":"skipped","error":"an earlier block failed"}`.
  Expected behavior: a failure whose submitted source begins with a literal
  outermost `try:` should roll back only that frame and leave the session
  usable, including when parsing fails inside the protected block. Current
  workaround: restart `target/release/litex -compact -session -before
  textbooks/Analysis2/chapter02-continuous-functions.lit` and replay accepted
  Chapter 2 statements. Root-cause class: `litex_blocker`. Primary label:
  `kernel_problem`.

- **Recursive function inside a parameterized template fails when used.**
  Minimal attempted shape:

  ```litex
  template<n N_pos, x, y \finite_real_vector<n>>:
      have fn linf_distance_partial(k closed_range(1, n)) R by induc k from 1:
          case k = 1: abs(x(1) - y(1))
          case k > 1: finite_set_max(union({linf_distance_partial(k - 1)}, {abs(x(k) - y(k))}))

  template<n N_pos>:
      have fn linf_distance(x, y \finite_real_vector<n>) R =
          \linf_distance_partial<n, x, y>(n)
  ```

  Exact verifier behavior: the template declaration itself reports success,
  but instantiation fails with
  `WellDefinedError: function 'linf_distance_partial' not defined`.
  Desired interface: recursive template functions should retain their local
  recursive binding when instantiated. Current workaround: the chapter
  exposes `linf_distance` through a trusted unique-maximum relation.
  Root-cause class: recursive template instantiation/name resolution. Primary
  label: `kernel_problem`.

- **Generic dependent unique selection does not yield a usable metric limit.**
  Attempt 1 used `have fn metric_limit by exist!` with parameters
  `X set`, `dist fn(x,y X) R`, and `u fn(n N_pos) X`. Exact verifier behavior:
  `have_fn_by_forall_exist_unique: forall parameter types must all be Obj`.
  Attempt 2 moved `X,dist` into a template; the template declaration reported
  success, but the immediate fact
  `$has_metric_limit(X,dist,u,\metric_limit<X,dist>(u))` was unknown after
  instantiation. Desired interface: a selected limit function on convergent
  sequences whose selection certificate is available to callers. Current
  workaround: keep the candidate relation and convergence existence predicate
  public, and do not expose a selected metric limit yet. Root-cause class:
  dependent unique selection/template certificate propagation. Primary label:
  `kernel_problem`.

- **Template-membership unfolding depends on prior `by extension` execution.**
  Attempt: in the `chap1` source context, a checked `by extension` for the
  first equality of Corollary 1.2.11 was followed by a local claim beginning
  `forall z \metric_closure<X, dist>(E)`. Its first fact,
  `$is_metric_adherent_point(X, dist, E, z)`, failed with
  `VerifyError: verification failed` (`type: prop fact`, Chapter 1 line 491).
  The same claim succeeds before the `by extension` block and in a release
  session at the project root. Desired behavior: an extension proof must not
  change the later template-membership unfolding context. Current workaround:
  establish both pairs of inclusion claims before either extension proof.
  Root-cause class: chapter-namespace proof-context restoration. Primary
  label: `kernel_problem`.

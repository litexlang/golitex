# Analysis II translation blockers

## Task context

- Task: Plan and implement Tao's *Analysis II* as a Litex textbook project.
- Scope: The source in `scripts/Analysis2/Analysis II.txt`, the working
  translation records, and the proposed `textbooks/Analysis2/` project.
- Related workspace: `scripts/Analysis2/` and `textbooks/Analysis2/`.

Add an item here only after a direct Litex attempt. Every item must include the
attempted statement or minimal Litex example, the exact verifier behavior when
available, the desired interface, a root-cause class, and the primary Litex
label `trust` or `kernel_problem`.

## do_not_know_how_to_formalize

- **Chapter 1 source proofs remain explicit proof debt.**
  Attempt: all 32 named items were translated in
  `textbooks/Analysis2/chapter01-metric-spaces.lit`, and the definitions plus
  representative use probes were run in the real caller context. Exact
  command:
  `target/debug/litex -runner -r textbooks/Analysis2`.
  Result: wrapper JSON `"result": "success"`, with 48 explicit `trust`
  statements. Desired state: replace each source-local theorem trust with a
  checked proof while preserving the current declaration shapes. Root cause:
  omitted exercise proofs, finite choice constructions, finite-dimensional
  norm estimates, and the source's compact open-cover argument have not yet
  been formalized. Primary label: `trust`.

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

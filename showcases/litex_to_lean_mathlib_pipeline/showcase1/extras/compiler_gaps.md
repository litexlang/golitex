# Showcase compiler gaps

## Main-pipeline adapter boundary

### Generated `Litex.Same` to native `Finset.Icc` equality

- Generated fact: `__Compiler_main.sum_first_odds` proves the inclusive
  integer sum is semantically equal to the complex rendering of `n^2`.
- Current usable route: `Adapter.lean` genuinely cites that fact and exposes
  a shorter Lean-facing theorem whose conclusion remains `Litex.Same`.
- Missing route: the public semantic wrapper layer does not currently expose
  a proved eliminator that turns this exact numeric `Litex.Same` into
  `∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2`.
- Rejected workaround: importing the generated module but proving the native
  theorem again by `Int.leInduction`; that does not consume generated proof
  evidence.
- Acceptance: derive the native Mathlib theorem from
  `__Compiler_main.sum_first_odds` through a reviewed, axiom-free numeric
  wrapper bridge, then check both adapter and downstream theorem with
  `lake env lean`.
- Primary blocker: `kernel_problem`.

## Property-flow Result consumers

## Task context

- Task: add property-centered Litex examples to explain the Litex → Lean → Mathlib flow
- Scope: `extras/property_flow.lit` and its future generated Lean module
- Related workspace: `showcases/litex_to_lean_mathlib_pipeline/showcase1`

## kernel_problem

### `property_flow.lit:square_of_is_nonnegative`: compile a concrete-prop premise

- Example attempted:

  ```litex
  thm square_of_is_nonnegative:
      ? forall value, root Z:
          $is_square_of(value, root)
          =>:
              value >= 0
      root^2 >= 0
  ```

- What happened: Litex strict verification succeeds, but
  `stmt_result_to_lean_compiler` stops at statement Result 5 with
  `defined-predicate inference component 2 changed its conclusion`.
- Expected behavior: compile the predicate-projected equality
  `value = root^2` under the theorem premise and use it to transport
  `root^2 >= 0` to the theorem conclusion.
- Follow-up: add a Result-owned named-theorem consumer for concrete-predicate
  premise components without reconstructing or changing their conclusions.
- Acceptance: compile `property_flow.lit` without holes, then submit the
  generated file to `lake env lean`.
- Primary blocker: `kernel_problem`.

### `property_flow.lit:sum_first_odds_is_square_of_n`: compile local theorem selection and definition folding

- Example attempted:

  ```litex
  thm sum_first_odds_is_square_of_n:
      ? forall n Z:
          n >= 1
          =>:
              $is_square_of(sum(1, n, kth_odd), n)
      by thm sum_first_odds(n) => sum(1, n, kth_odd) = n^2
      by def $is_square_of(sum(1, n, kth_odd), n)
  ```

- What happened: the exact source verifies, but an isolated compiler probe
  without the earlier predicate-premise theorem stops on the first local step
  with `named forall proof step 1 has no local compiler consumer`.
- Expected behavior: cite the retained `sum_first_odds` FactId, compile its
  instantiated equality, then fold the checked predicate clause.
- Follow-up: add local `by thm` and `by def` consumers to named `forall`
  compilation, preserving source order and FactIds.
- Acceptance: the generated theorem directly cites the generated
  `sum_first_odds` theorem and unfolds only the generated predicate definition.
- Primary blocker: `kernel_problem`.

### existential `is_integer_square`: compile predicate-backed local witness elimination

- Example attempted:

  ```litex
  prop is_integer_square(value Z):
      exist root Z st {value = root^2}

  thm integer_square_nonnegative:
      ? forall value Z:
          $is_integer_square(value)
          =>:
              value >= 0
      obtain root from $is_integer_square(value)
      root^2 >= 0
  ```

- What happened: Litex strict verification succeeds, including witness
  elimination and equality transport, but compilation reports
  `named forall proof step 1 has no local compiler consumer` for the `obtain`.
- Expected behavior: compile the verifier-owned existential witness and body
  evidence locally, without introducing an axiom or project proof hole.
- Follow-up: add the local predicate-backed `obtain` Result consumer after the
  simpler two-argument relation flow is generated end to end.
- Acceptance: replace the supplied-witness relation with the existential
  wrapper in a generated example and pass the real Lean kernel gate.
- Primary blocker: `kernel_problem`.

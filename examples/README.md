# Litex Examples

Phase-oriented acceptance tree for the current Litex pipeline (`src/`).

> **When extending or repairing an example, use one `-session` and keep its
> accepted context after an ordinary failure. Do not rerun the whole file after
> every few new lines.** The [Agent Guide](../docs/AgentGuide.md) shows a short
> comparison and the restart/replay boundaries. Clean file commands below are
> baseline, checkpoint, and final acceptance gates.

## Layout

```text
examples/
  proof_nodes/          verify / searched_proof tracers
  stmt_nodes/           exec_stmt arms
  wd/  wd_negative/     well-definedness positives / must-fail
  equal_negative/       equality must-fail probes
  infer/                store → Infer*Result consequences
  tokenize/             tokenizer / Unicode input surface
  module_manager/       -r / -f / litex.config mount
  agent_session_demo/    Python driver for persistent-Session authoring
  knowledge_base/       persist / restore goldens
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

Real sequence limit tracers:

- [Explicit epsilon-N proof for 1/k, then selected-value use](wd/sequence_limit.lit).
- [Equivalent seq(R) / fn(k N+) R and finite-existence interfaces](wd/sequence_limit_interfaces.lit).
- [Common sequence-limit proofs](wd/sequence_limit_common_proofs.lit): explicit `1/n -> 0`, rational examples, `sin(n)/n -> 0`, `sqrt(1+1/n) -> 1`, and `(1/2)^n -> 0`; also finite initial changes, even-index subsequences, eventual positivity/nonzero terms, and divergence of `n`. Each convergence proof precedes `lim` use.
- [Limit rules and their premises](../docs/sequence-limits.md), with one `seq_limit_*.lit` example per theorem in `stmt_nodes/release_and_expand/builtin_thm/`.

Finite-point real function limit tracers:

- [Explicit punctured epsilon-delta proof, then selected-value use](wd/real_function_limit_at.lit): `x^2/x` at zero without calling the function at zero.
- [Polynomial and rational limit proofs](wd/real_function_limit_common_proofs.lit), [relative endpoint](wd/real_function_limit_endpoints.lit), and [existence/congruence interfaces](wd/real_function_limit_interfaces.lit).
- [All 22 rules and their domain premises](../docs/function-limits.md), with one `fn_limit_at_*.lit` example per theorem in `stmt_nodes/release_and_expand/builtin_thm/` and `real_function_limit_*.lit` rejection controls in `wd_negative/`.

## Other

- [Python Session agent loop](agent_session_demo/README.md) drives the real CLI,
  checks recovery after a rejected statement, and compares dependent-prefix
  verification counts.
- `_internal/` is developer material (including larger case-study regressions),
  not the public reading path.
- Earlier Litex-to-Lean pairs are archived locally under
  `scripts/legacy_to_lean/lean/examples/`, which is excluded from Git.

Standalone regression examples:

- [Claim/obtain scope](claim_obtain_scope.lit).
- [Nonempty-set property arguments](nonempty_set_property_arguments.lit).
- [Function construction by unique existence](have_fn_by_unique_existence.lit).
- [Object-definition equalities](object_definition_equalities.lit).
- [Template-defined type interfaces](stmt_nodes/definition/template_type_interfaces.lit).
- [Inverse trigonometric principal intervals](inverse_trig_principal_intervals.lit).

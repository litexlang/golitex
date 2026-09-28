# new_pipeline example tracers

Phase-oriented acceptance suite for `src/new_pipeline/`.
One user-visible kernel stage → one subdirectory (not a raw mirror of every Rust module).

```text
examples/new_pipeline/
  proof_nodes/      verify / searched_proof (ByBuiltinRule, Known*, …)
  stmt_nodes/       exec_stmt arms (definition / witness / by / unsafe)
  wd/               Obj/Fact well-definedness positives
  wd_negative/      WD must-fail tracers
  equal_negative/   equality must-fail probes (e.g. no family_intersect({})={})
  infer/            store → Infer*Result consequences
                    (kernel: `src/new_pipeline/store_fact_and_infer/README.md`)
  tokenize/         tokenizer surface (line continuation, …)
  module_manager/   -r / -f / litex.config mount
  knowledge_base/   persist / restore (DefProp JSON goldens, later lkb)
```

Legacy public reading path (`examples/01_…` … `09_…`) stays outside this tree.

## Acceptance

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <this-file>
```

Exit 0 (or intentional non-zero for `wd_negative` / `equal_negative`) is the gate.
Each subdirectory README has a `find … | sort` run-all snippet.

## Writing

- Prefer **new** `.lit` for a new/widened rule; do not leave acceptance only in `examples/tmp.lit`.
- `proof_nodes` / `wd`: prefer `have` / `let` / `forall`; avoid `trust` when possible.
- `infer`: seed with store, then assert the inferred consequence.
- `stmt_nodes/unsafe`: trust-stmt coverage.

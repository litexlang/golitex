# Litex Examples

Phase-oriented acceptance tree for the current Litex pipeline (`src/`).

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
  knowledge_base/       persist / restore goldens
  _internal/            fixtures / drafts / non-public regressions
  tmp.lit               scratch
```

## Acceptance

```bash
target/release/litex -f examples/knowledge_base/def_prop/is_pos.lit
target/release/litex -f <any-file-under-phase-dirs>
```

Exit 0 (or intentional non-zero for `wd_negative` / `equal_negative`) is the gate.
Each subdirectory README has a `find … | sort` run-all snippet.

One user-visible kernel stage → one subdirectory. Prefer a **new** `.lit` for a
new/widened rule; do not leave acceptance only in `tmp.lit`.

## Other

- `_internal/` is developer material (including larger case-study regressions),
  not the public reading path.
- Litex-to-Lean pairs live under [`lean/examples/`](../lean/examples/).

# new_pipeline stmt-node tracers

One wired `exec_stmt` arm → one `.lit` file.
File names mirror Rust `Stmt` / `DefinitionStmt` / `ByStmt` / `UnsafeStmt` variants.

Fact **search** paths live in `../new_pipeline_proof_nodes/`. This suite only
checks that each currently wired statement kind can execute end-to-end.

## Acceptance

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <this-file>
```

Exit 0 is enough. Stub / not-yet-wired stmt arms are **omitted**.

## Layout

```text
fact/          Stmt::Fact
definition/    LetObj, HaveObj*, HaveFn*, ObtainObjFromExistFact,
               ObtainObjFromAtomicFact, ObtainObjFromThm, DefProp,
               DefAbstractProp, DefStruct*, DefTemplate (incl. obtain body),
               DefThm, ReleaseObjDef, ReleaseStructDef, ReleaseThm
witness/       WitnessExistFact (no indented body in new_pipeline)
unsafe/        TrustStmt, TrustHaveStmt
by/            ByReflexive/Symmetric/TransitiveProp, Extension, Enumerate*,
               For, Contra, Cases, Def, Thm, Induc, StrongInduc,
               RegularityAxiom, AxiomOfChoice
```

Omitted for now: `by zorn_lemma` (wired; chain-upper-bound obligation still
needs a green tracer). Parse-only / unwired: claim/example/sketch/try,
eval, setting, axiom, strategy.
`obtain … from exist` / `exist!` / `$P` / `thm` is wired (see `definition/obtain_*.lit`
and `definition/def_template_obtain_from_*.lit`).

## Run all

```bash
export PATH="/usr/bin:/bin:$PATH"
fail=0
while IFS= read -r f; do
  echo "=== $f ==="
  LITEX_NEW_PIPELINE=1 target/release/litex -f "$f" || fail=1
done < <(find examples/new_pipeline_stmt_nodes -name '*.lit' | sort)
exit $fail
```

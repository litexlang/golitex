# new_pipeline stmt-node tracers

One wired `exec_stmt` arm → one `.lit` file.
File names mirror Rust `Stmt` / `DefinitionStmt` / `ByStmt` / `UnsafeStmt` variants.

Fact **search** paths live in `../proof_nodes/`. This suite only
checks that each currently wired statement kind can execute end-to-end.

## Acceptance

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <this-file>
```

Exit 0 is enough. Stub / not-yet-wired stmt arms are **omitted**.

## Layout

```text
fact/          Stmt::Fact
definition/    LetObj, HaveObj*, HaveByFnPreimage, HaveByReplacementAxiom, HaveFn*,
               ObtainObjFromExistFact, ObtainObjFromAtomicFact,
               DefProp, DefAbstractProp, DefStruct*,
               DefTemplate (incl. obtain / have-by-replacement_axiom body), DefThm,
               ReleaseObjDef, ReleaseStructDef, ReleaseThm
witness/       WitnessExistFact, WitnessExistUnique (via exist!),
               WitnessAtomicFact, WitnessNonemptySet
               (no indented body in new_pipeline; no FnSet shortcut)
unsafe/        TrustStmt, TrustHaveStmt
by/            ByReflexive/Symmetric/TransitiveProp, Extension, Enumerate*,
               For, Contra, Cases, Def, Thm, Induc, StrongInduc,
               RegularityAxiom, AxiomOfChoice
```

Omitted for now: `by zorn_lemma` (wired; chain-upper-bound obligation still
needs a green tracer). Parse-only / unwired: claim/example/sketch/try,
eval, axiom, strategy.
`obtain … from exist` / `exist!` / `$P` is wired (see `definition/obtain_*.lit`
and `definition/def_template_obtain_from_*.lit`).
`have by replacement_axiom` is wired (see `definition/have_by_replacement_axiom.lit`
and `definition/def_template_have_by_replacement_axiom.lit`).
`have by fn_preimage` is wired (see `definition/have_by_fn_preimage.lit`).

## Run all

```bash
export PATH="/usr/bin:/bin:$PATH"
fail=0
while IFS= read -r f; do
  echo "=== $f ==="
  LITEX_NEW_PIPELINE=1 target/release/litex -f "$f" || fail=1
done < <(find examples/new_pipeline/stmt_nodes -name '*.lit' | sort)
exit $fail
```

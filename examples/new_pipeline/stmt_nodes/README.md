# new_pipeline stmt-node tracers

One wired `exec_stmt` arm → one `.lit` file.
File names mirror Rust `Stmt` family variants
(`Definition` / `Release` / `By` / `Register` / …).

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
definition/    Definition: DefineObj (let/have/obtain/have by…) plus
               flat siblings (prop/thm/struct/template/have fn…);
               also Release* tracers live nearby in this tree
witness/       WitnessExistFact, WitnessExistUnique (via exist!),
               WitnessAtomicFact, WitnessNonemptySet
               (no indented body in new_pipeline; no FnSet shortcut)
unsafe/        TrustBoundary (trust / trust have)
register/      RegisterReflexive/Symmetric/TransitiveProp
by/            Extension, Enumerate*, For, Contra, Cases, Def, Thm,
               Induc, StrongInduc, RegularityAxiom, AxiomOfChoice
proof_block/   Claim, Sketch
```

## What / how (wired arms)

| Folder / file | What | How (surface) |
|---|---|---|
| `fact/` | Assert a fact | bare `1 + 1 = 2` |
| `definition/let_obj.lit` | Equality binding | `let a = expr` |
| `definition/have_obj_*.lit` | Introduce typed objs | `have x R` / `= expr` / `:` body |
| `definition/obtain_*.lit` | Name exist witnesses | `obtain a from exist …` / `$P` |
| `definition/have_by_*.lit` | Preimage / Replacement | `have by fn_preimage:` / `replacement_axiom:` |
| `definition/have_fn_*.lit` | Define named functions | `have fn … =` / `by cases` / `by induc` / `by exist!` |
| `definition/def_prop.lit` | Concrete predicate | `prop P(x A):` body |
| `definition/def_abstract_prop.lit` | Abstract predicate | `abstract_prop P(x, y)` |
| `definition/def_struct*.lit` | Struct carrier | `struct Point:` fields |
| `definition/def_template*.lit` | Parameterized def | `template<A set>:` one body |
| `definition/def_thm.lit` | Named theorem | `thm name: ? fact` + proof |
| `definition/release_*.lit` | Unpack packaged facts | `release thm` / `struct def` / `obj def` |
| `unsafe/` | Trust boundary | `trust:` / `trust have …:` |
| `register/` | Prop rewrite laws | `register reflexive\|symmetric\|transitive:` |
| `witness/` | Exhibit witnesses | `witness exist … from …:` etc. |
| `by/` | Named proof methods | `by cases:` / `by contra:` / … |
| `proof_block/` | Nested scopes | `claim:` / `sketch:` |

Full human catalog: `docs/Manual.md` → Statements → Preview Stmt catalog.
Parse dispatch: `src/new_pipeline/parse/README.md`.

Omitted for now: `by zorn_lemma` (wired; chain-upper-bound obligation still
needs a green tracer). Parse-only / unwired: eval, axiom, strategy.
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

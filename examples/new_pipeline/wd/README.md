# new_pipeline well-definedness gallery

Positive tracers for **already-implemented** Obj / Fact WD.
Negatives stay in `../wd_negative/`.

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <this-file>
```

## Status (Obj) — after Wave4 (Sum/Product/Reduce + Index* full type + FieldAccess FnObj)

| Status | What |
|--------|------|
| **Done** | Scalar P0; Identifier (defined check); Identifier-headed `FnObj`; **AnonymousFnLiteral-headed `FnObj`**; **FieldAccess-headed `FnObj`** (field FnSet type / InFunctionSet domain); binder `FnSet`/`AnonymousFn`/`SetBuilder`; `CartDim`/`Proj`/`TupleDim`/`ObjAtIndex`; `ListSet` pairwise `!=`; `FiniteSetSize`/`Max`/`Min`; `Range`/`ClosedRange` (∈Z); Interval/Ray (∈R); `FnRange` (∈FnSet); IndexUnion/Intersect + IndexCart `$is_set`/`nonempty` + **full `family $in fn(...)`**; FiniteSeqSet/SeqSet light `$is_set`(+`n∈N`); **Sum/Product** (Z + `start<=end` + ret ⊆ C + light coverage); **Reduce** (Z + homogeneous op + seed ∈ carrier); StructObj / FieldAccess / InstantiatedTemplateObj (tracers under `obj/`) |
| **Leaf / children-only OK (legacy also)** | `Number`/`π`/`i`/`e`/`StandardSet`; `Union`/`Intersect`/`SetMinus`/`FamilyUnion`/`FamilyIntersect`; `PowerSet`; `Cart`/`Tuple` |
| **Still TODO** | Sum/Product/Reduce **full** legacy binder depth (local interval body re-check under `start<=i<=end`, enumerated coverage, finite-aggregate elementwise apps, reduce assoc/comm laws); deeper Struct/Template edge cases beyond current tracers |

## Status (Fact)

| Status | What |
|--------|------|
| **Dispatcher done** | All Fact shapes route |
| **Real binder WD** | Forall / Exist / NotForall |
| **Mostly Obj routing** | Equal / Atomic / And / Or / Chain |

## Layout

```text
obj/     done Obj WD families
fact/    done Fact WD shapes
```

## Run all positives

```bash
export PATH="/usr/bin:/bin:$PATH"
fail=0
while IFS= read -r f; do
  echo "=== $f ==="
  LITEX_NEW_PIPELINE=1 target/release/litex -f "$f" || fail=1
done < <(find examples/new_pipeline/wd -name '*.lit' | sort)
exit $fail
```

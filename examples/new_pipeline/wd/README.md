# new_pipeline well-definedness gallery

Positive tracers for **already-implemented** Obj / Fact WD.
Negatives stay in `../new_pipeline_wd_negative/`.

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <this-file>
```

## Status (Obj) — after Identifier / FnRange / Index* InFunctionSet half

| Status | What |
|--------|------|
| **Done** | Scalar P0; Identifier (defined check); Identifier-headed `FnObj`; **AnonymousFnLiteral-headed `FnObj`** (literal FnSet + dom); binder `FnSet`/`AnonymousFn`/`SetBuilder`; `CartDim`/`Proj`/`TupleDim`/`ObjAtIndex`; `ListSet` pairwise `!=`; `FiniteSetSize`/`Max`/`Min`; `Range`/`ClosedRange` (∈Z); Interval/Ray (∈R); `FnRange` (∈FnSet); IndexUnion/Intersect + IndexCart `$is_set`/`nonempty` + family ∈ FnSet (registration half); FiniteSeqSet/SeqSet light `$is_set`(+`n∈N`) |
| **Leaf / children-only OK (legacy also)** | `Number`/`π`/`i`/`e`/`StandardSet`; `Union`/`Intersect`/`SetMinus`/`FamilyUnion`/`FamilyIntersect`; `PowerSet`; `Cart`/`Tuple` |
| **Still TODO** | Sum/Product/Reduce (iteration binder); Index*/IndexCart full `family $in fn(...)` type check; Struct/Template depth; FnObj `FieldAccess` head domain (template already on InFunctionSet path) |

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
done < <(find examples/new_pipeline_wd -name '*.lit' | sort)
exit $fail
```

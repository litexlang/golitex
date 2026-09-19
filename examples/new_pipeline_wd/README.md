# new_pipeline well-definedness gallery

Positive tracers for **already-implemented** Obj / Fact WD.
Negatives stay in `../new_pipeline_wd_negative/`.

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <this-file>
```

## Status (Obj) — after Option 1 light fill

| Status | What |
|--------|------|
| **Done** | Scalar P0; Identifier-headed `FnObj`; binder `FnSet`/`AnonymousFn`/`SetBuilder`; `CartDim`/`Proj`/`TupleDim`/`ObjAtIndex`; `ListSet` pairwise `!=`; `FiniteSetSize`/`Max`/`Min`; `Range`/`ClosedRange` (∈Z); Interval/Ray (∈R); IndexUnion/Intersect + GeneralCart light `$is_set`/`nonempty` half; FiniteSeqSet/SeqSet light `$is_set`(+`n∈N`) |
| **Leaf / children-only OK (legacy also)** | `Number`/`π`/`i`/`e`/`StandardSet`; `Union`/`Intersect`/`SetMinus`/`Big*`; `PowerSet`; `Cart`/`Tuple`; `FiniteSeqList` |
| **Still TODO** | Sum/Product/Reduce (iteration binder); FnRange (known fn body); Replacement (prop+uniqueness); Index*/GeneralCart full family∈FnSet; Struct/Template; Identifier undefined Fail; FnObj non-Identifier heads |

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

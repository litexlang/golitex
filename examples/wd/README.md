# Well-definedness gallery

Positive tracers for **already-implemented** Obj / Fact WD.
Negatives stay in `../wd_negative/`.

```bash
target/release/litex -f <this-file>
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

[Predicate signature preflight](predicate_signature_preflight.lit) preserves
legal local proof helpers and later same-name declarations. Ordinary predicate
WD additionally resolves the complete owner-qualified name and checks exact
arity before assumptions or proof bodies use the fact. Executable undefined,
arity, rollback and imported-cache controls live in
`tests/unit/execute/predicate_signature_wd/tests.rs` and
`src/run_module/cross_file_identity_tests.rs`. Builtin predicate domain checks
are a separate migration audit; this tracer does not establish their parity.

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
  target/release/litex -f "$f" || fail=1
done < <(find examples/wd -name '*.lit' | sort)
exit $fail
```

## Dependent quantifier parameters

[dependent_parameters.lit](fact/dependent_parameters.lit) covers `claim` and
`thm` goals whose later parameter carriers refer to earlier parameters, such
as `A nonempty_set, a A` and `A nonempty_set, f fn(x A) A`. The verifier checks
and introduces one group at a time inside the existing local WD scope. The
same ordering is used for forall, forall-iff, not-forall, and existential WD;
this does not prove a quantified conclusion or leak its bound parameters.

- [Original group left cancellation](fact/group_left_cancel.lit): dependent carriers and the complete original theorem proof.

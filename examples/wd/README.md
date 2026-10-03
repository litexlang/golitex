# Well-definedness gallery

Positive tracers for **already-implemented** Obj / Fact WD.
Negatives stay in `../wd_negative/`.

[Instantiated function fields](struct_field_instantiation.lit) check generic,
concrete, nested and dependent header arguments in named theorem goals. Field
types use the selected struct's actual parameters. This does not open nested
struct laws; argument carriers and callable guards remain mandatory. Executable
negative controls live in `tests/unit/execute/struct_field_instantiation/tests.rs`.

[Finite extrema](finite_extrema_real_carrier.lit) require all three conditions:
finiteness, nonemptiness, and `S $subset R`. Real literals, aliases and checked
generic domains remain valid; `{i}` is rejected by the
[non-real extrema control](../wd_negative/finite_extrema_nonreal.lit).

[Finite-set fold domains](finite_set_fold_domain.lit) checks that the iterand's
declared domain and predicates cover every set element. Wrong-domain and
predicate counterexamples reject before binding. Associativity/commutativity
enforcement remains a separate gap; ordered `reduce` may use subtraction.

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

## Function returns and struct arguments

[Function returns and struct arguments](obj/return_and_struct_domains.lit)
checks valid identity, wider, guarded and dependent return carriers, and typed
struct header arguments. Every anonymous-function body must prove membership
in its return set, including a body that is just a parameter. Struct-instance
WD proves substituted header types, including the three set kinds and
dependent element domains. The executable rejection controls are
[`function_projection_return_domain.lit`](../wd_negative/function_projection_return_domain.lit)
and [`struct_argument_domain.lit`](../wd_negative/struct_argument_domain.lit);
failed statements leave no binding or successful WD cache entry.

## Dependent quantifier parameters

[dependent_parameters.lit](fact/dependent_parameters.lit) covers `claim` and
`thm` goals whose later parameter carriers refer to earlier parameters, such
as `A nonempty_set, a A` and `A nonempty_set, f fn(x A) A`. The verifier checks
and introduces one group at a time inside the existing local WD scope. The
same ordering is used for forall, forall-iff, not-forall, and existential WD;
this does not prove a quantified conclusion or leak its bound parameters.

- [Original group left cancellation](fact/group_left_cancel.lit): dependent carriers and the complete original theorem proof.

[Guarded quantifier domains](fact/guarded_quantifier_domains.lit) checks
`not forall` and `forall … <=>:` definitions, plus a `claim` goal. A domain
fact is checked before being assumed in the retained binder scope; later
domains and conclusions may use it for WD. Neither iff branch is assumed
while checking the other. Missing guards, zero denominators and iff cross-branch
assumptions have executable controls in `../wd_negative/quantifier_domain_*.lit`.

[Function application evidence](obj/application_evidence_ownership.lit) covers
named, literal and field-headed calls with repeated composite arguments.
Discarded candidate scopes cannot own WD ids in the returned proof. The Rust
regression resolves child and projected WD citations after the statement ends,
including reuse of an existing caller-owned cache entry.

`predicate_positive_integer_carrier.lit` checks strict positive-integer introduction from a known integer carrier and positive bound. Its closed negative carrier controls (`1 / 2` in Z/N/N+) run separately in `cargo test --release predicate_domain`; premise-producing N+ rules must obey ordinary builtin entry permission.

[gcd_nonzero_disjunction.lit](gcd_nonzero_disjunction.lit) checks GCD's domain
using a proved `x != 0 or y != 0`, without choosing either operand. The same
domain evidence supports the definition inferred from `$coprime(x, y)`.
`cargo test --release predicate_domain` also rejects `gcd(0, 0)` and checks
that local assumptions do not escape.

[nullary_predicate_signature.lit](nullary_predicate_signature.lit) defines and
uses `prop ready()` with zero parameters. Signature regressions reject extra
arguments, undefined goals and ill-defined bodies; nullary `abstract_prop`
retains its strict-mode restriction.

[signed_conjunctions.lit](signed_conjunctions.lit) checks positive and negative
atomic conjuncts, a leading negative disjunct, existential bodies and repeated
atomic negation. Every atom still undergoes signature/domain WD. Negated
comparison chains and `not exist!` keep their existing syntax restrictions.

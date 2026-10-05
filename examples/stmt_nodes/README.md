# Stmt-node tracers

One wired `exec_stmt` arm → one `.lit` file.
File names mirror Rust `Stmt` family variants
(`Definition` / `Release` / `By` / `Register` / …).

Fact **search** paths live in `../proof_nodes/`. This suite only
checks that each currently wired statement kind can execute end-to-end.

## Acceptance

```bash
target/release/litex -f <this-file>
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
               (checked optional proof body; no FnSet shortcut)
unsafe/        TrustBoundary (trust / trust have)
register/      RegisterReflexive/Symmetric/TransitiveProp
by/            Extension, EnumerateFiniteSet, For, Contra, Cases, Def, Thm,
               Induc, StrongInduc
release_and_expand/  ExpandRange, ReleaseAxiomOfChoice, ReleaseRegularityAxiom,
               ReleaseZornLemma
               (plus release thm/struct/obj live under definition/)
proof_block/   Claim, Sketch
command/       Eval (exact evaluation, checked algorithm equations, result equality storage)
```

## What / how (wired arms)

| Folder / file | What | How (surface) |
|---|---|---|
| `fact/` | Assert a fact | bare `1 + 1 = 2` |
| [fact/negative_leading_code.lit](fact/negative_leading_code.lit) | Source starts with a negative number | `-e '-2 < 0'` preserves the complete source operand; `-2 > 0` rejects |
| `definition/let_obj.lit` | Equality binding | `let a = expr` |
| [definition/let_template_struct_aliases.lit](definition/let_template_struct_aliases.lit) | Template and nested callable-field aliases | Open the inner carrier with `release struct def space.scalars` before invoking its `let` alias; struct fixtures use at least two fields |
| `definition/have_obj_*.lit` | Introduce typed objs | `have x R` / `= expr` / `:` body |
| `definition/parse_scope_transaction.lit` | Correct a previously failed declaration in the same Runtime | failed `have k N = -1`, then active `have k N = 1`; negative boundary in `tests/unit/run/binding_lifecycle/tests.rs` |
| `definition/obtain_*.lit` | Name exist witnesses | `obtain a from exist …` / `$P` |
| `definition/have_by_*.lit` | Preimage / Replacement | `have by fn_preimage:` / `replacement_axiom:` |
| [definition/field_function_preimage.lit](definition/field_function_preimage.lit) | Preimage of a checked callable field | Retain `ops.op` as the application head and preserve source, arity and guard checks |
| `definition/have_fn_*.lit` | Define named functions | `have fn … =` / `by cases` / `by induc` / `by exist!` |
| `definition/def_algo.lit` | Algo fn + executable cases | `algo f(x R) R by cases:` … |
| [command/eval_store_result.lit](command/eval_store_result.lit) | Compute and publish the result equality | `eval sum(0,3,flag)` stores `sum(0,3,flag)=3` for later proof; failure rolls back |
| `definition/def_prop.lit` | Concrete predicate | `prop P(x A):` body |
| `definition/def_abstract_prop.lit` | Abstract predicate | `abstract_prop P(x, y)` |
| [definition/strict_abstract_prop.lit](definition/strict_abstract_prop.lit) | Abstract signature in strict mode | declaration and `P(x) => P(x)` pass; unproved instances and user trust do not |
| `definition/def_struct*.lit` | Struct carrier | `struct Point:` fields |
| `definition/def_template*.lit` | Parameterized def | `template<A set>:` one body |
| [definition/template_definition_facts.lit](definition/template_definition_facts.lit) | Publish template definition facts | `forall` over template arguments, with body and header premises retained |
| [definition/template_alias_struct_tuple.lit](definition/template_alias_struct_tuple.lit) | Template aliases and named tuple results | Checked callable signatures and stored value paths reach struct fields |
| `definition/def_thm.lit` | Named theorem | `thm name: ? fact` + proof |
| `definition/axiom.lit` | Named axiom (trusted forall) | `axiom name: ? forall …` |
| `definition/def_strategy.lit` | Named strategy (proved forall) | `strategy name: ? forall …` + proof; later `$P` via known_strategy |
| `definition/def_strategy_peel_sum.lit` | known_strategy peel | binary `$is_pos(a+b)` package → `$is_pos(a+b+c+d)` without intermediate sums |
| `definition/release_*.lit` | Unpack packaged facts | `release thm` / `struct def` / `obj def` |
| `definition/theorem_call_typed_arguments.lit` | Check explicit theorem argument types | `release thm` / `by thm … =>` with typed binders |
| `release_and_expand/` | Expand range / release axioms | `expand:` / `release axiom_of_choice` / `release regularity_axiom` / `release zorn_lemma` |
| `unsafe/` | Trust boundary | `trust:` / `trust have …:` |
| `register/` | Prop rewrite laws | `register reflexive\|symmetric\|transitive:` |
| `witness/` | Exhibit witnesses | `witness exist … from …:` etc. |
| `witness/witness_type_soundness.lit` | Check concrete witness and predicate argument types | `witness exist` / `witness $P(args)` |
| `by/` | Named proof methods | `by cases:` / `by contra:` / … |
| [by/by_contra_classified_goals.lit](by/by_contra_classified_goals.lit) | Classified compound contra targets | `exist` / `not exist`, `or`, QF `forall` / `not forall`; atomic `impossible` |
| [by/by_contra_unique_existence.lit](by/by_contra_unique_existence.lit) | Unique-existence contra target | Existing forall/exists reverse assumption; distinct alternative witness |
| [by/by_contra_forall_iff.lit](by/by_contra_forall_iff.lit) | Whole iff contra target | Existing QF equivalence failure and Exist counterexample |
| [by/by_contra_compound_impossible.lit](by/by_contra_compound_impossible.lit) | Compound closing facts | Checked Exist/NotExist contradiction and multiline Forall closing; both proofs required |
| [by/by_contra_imaginary_unit.lit](by/by_contra_imaginary_unit.lit) | Imaginary-unit contradiction with explicit substitution | `i*i = 0*0 = 0` supplies the squared-zero side; the original `impossible i*i != 0` closes the proof |
| `by/induction_base_scope.lit` | Separate induction base and step scopes | `by induc` / `by strong_induc` |
| `proof_block/` | Nested scopes | `claim:` / `sketch:` |
| `by/finite_set_conditional_proof_steps.lit` | Conditional enumeration and nested proof steps | finite list guards, live binder names, and local nested `by def` |
| `unsafe/template_strict_policy.lit` | Strict template trust policy | ordinary run accepts; strict rejects template trust-have |
| `command/eval_source_domain.lit` | Source WD before eval | valid natural-domain calls compute; invalid calls reject |
| `command/eval.lit` | Display eval: closed-numeric rewrite + algo | `eval 3!` / `eval sqrt(4)` / `eval a + 1` / `eval nonzero_flag(0) + 1` |
| `command/eval_closed_numeric_complex.lit` | Nested closed-numeric display eval | `eval gcd(54,(-24))+3!*sqrt(4)` / rewrite `a+b*c` |

Full human catalog: `docs/Manual.md` → Statements → Preview Stmt catalog.
Parse dispatch: `src/parse/README.md`.

`release zorn_lemma` is wired (see `release_and_expand/release_zorn_lemma.lit`):
named upper-bound / maximality props are checked by IR alignment against the
exact forall shapes; obligations are fact-only in the body (trust them outside
first, same pattern as `release axiom_of_choice`).
`eval` rewrites via `known_closed_numeric_equal`, then recursively evaluates:
closed-numeric simplify, and plain-Identifier `FnObj` through a stored algo.
It does **not** store a proof fact. Recursive-algo examples are deferred.
Tracer: `command/eval.lit`.
Top-level `algo … by cases` / `by induc` is wired (see `definition/def_algo.lit`).
`obtain … from exist` / `exist!` / `$P` is wired (see `definition/obtain_*.lit`
and `definition/def_template_obtain_from_*.lit`).
`have by replacement_axiom` is wired (see `definition/have_by_replacement_axiom.lit`
and `definition/def_template_have_by_replacement_axiom.lit`).
`have by fn_preimage` is wired (see `definition/have_by_fn_preimage.lit`).
`axiom` is wired (see `definition/axiom.lit`); `release thm` / `by thm` resolve
axiom names the same way as theorems.
`strategy` is wired (see `definition/def_strategy.lit`): proves a `? forall`,
stores the named interface under `strategy_definitions`, and later non-equality
atomics may apply it via the `known_strategy` search stage (after by-definition,
before known forall). The forall is **not** injected into ordinary known_forall.

## Run all

```bash
export PATH="/usr/bin:/bin:$PATH"
fail=0
while IFS= read -r f; do
  echo "=== $f ==="
  target/release/litex -f "$f" || fail=1
done < <(find examples/stmt_nodes -name '*.lit' | sort)
exit $fail
```

### Induction binder recovery

[by_induc_order.lit](by/by_induc_order.lit) covers order, nested arithmetic,
and compound goals for `by induc` / `by strong_induc`. Recovery uses the
parser-assigned identifier wherever it occurs freely in the goals or proof
actions, including sets, tuples, functions, and comprehensions. A fresh ID is
used only for a genuinely unused variable. Base and successor obligations
still both require proof; nested binders keep their own identity.

[induction_collection_binders.lit](by/induction_collection_binders.lit) checks
those object shapes and constant goals. [induction_domain_and_proof_actions.lit](by/induction_domain_and_proof_actions.lit)
checks domain-aware goal WD and ordinary local proof actions. The local
declarations do not escape their induction case. Normal failure details name
base/step, goal WD, and the failed goal/proof-step index; Detailed results
retain both case proof trees.

[inductive_nested_cases.lit](definition/inductive_nested_cases.lit) checks
coverage and disjointness at every nested level under the parent guard.
The paired Rust tests execute the old overlapping/hole definitions and require
rejection before publication. [template_inductive_arithmetic.lit](definition/template_inductive_arithmetic.lit)
checks that recursive self calls inside arithmetic retain the exact template
instance. Its explicit smaller-call equality is a proof step; the existing
proof search may still need that step for recursive arithmetic evaluation.

Native builtin release tracers: `release_and_expand/builtin_thm/` contains one
strict runnable example for each of the 29 reserved theorem names. The
examples verify the actual required premises before release and then reuse
the conclusion. Parser migration tracers include
`fact/inline_forall_premise.lit` and
`by/induction_reuses_goal_parameter.lit`. Wrong arity, unsupported argument
shape, missing premises, selected-fact failure and transaction rollback are
covered by `src/execute/execute_by_stmt/builtin_thm/tests.rs`.

The internal [finite-set induction regression](../_internal/regression/finite_set_induction.lit) proves the mathematical principle through ordinary induction on cardinality. Its original empty-set and fresh-insertion inputs are explicit hypotheses; singleton removal and reconstruction provide the checked successor step, followed by the concrete {1,2} replay. It does not reintroduce the removed finite-set induction syntax.

## Witness Detailed evidence

The [witness evidence tracer](witness/witness_detailed_evidence.lit) checks an
atomic predicate with a local proof, dependent witness types, nonempty-set
membership, explicit unique witnesses, and a real function-space member.
Detailed retains the actual successful argument/WD/type/proof/body checks,
and the actual nonempty failure stage and child. Normal and execution verdicts
are unchanged; local_env remains omitted. The [source-owned note](experience/problem_notes/witness-detailed-evidence-2026-10-05.md)
records the strict file gate, focused tests and deliberate exclusion of the
legacy wrong-witness function-space shortcut.

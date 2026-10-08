# Statement regression tests

Task: detailed per-statement tests requested on 2026-10-01.
The authoritative inventory is `src/ast/stmt.rs`: 52 reachable statement
leaves, including `Stmt::Fact`. Each leaf has one primary `.lit` file with
multiple runnable scenarios. There are 174 positive scenarios,
141 negative scenarios, 24 additional boundary/regression checks, and no open
K-number gap reproduction. Each scenario runs independently;
each complete primary file also runs in a fresh process.

The [2026-10-06 tuple/cart acceptance](../proof_nodes/experience/problem_notes/tuple-cart-local-call-eval-2026-10-06.md)
checks the then-current 51 statement leaves in 383 CLI checks and passes the
actual-AST integration. Its separate basics gate passes 175 checks. The
[2026-10-03 audit](audit_2026-10-03.md) is a dated 377-check baseline;
separate kernel observations and semantic boundaries remain in that report.

The [2026-10-04 CLI/strict acceptance](experience/problem_notes/cli-source-strict-abstract.md)
allows pure abstract predicates in strict mode and fixes negative-leading `-e`
source. Its scoped tests preserve unproved-instance, WD, arity and trust rejection.
The dated 377-check scan above predates the added boundary.

The [eval publication acceptance](../test_objs/experience/problem_notes/eval_store_result_2026-10-04.md)
updates successful eval to store the checked source/result equality. The
[boundary fixture](boundaries/evaluation-stores-result.lit) and recursive/named
EvalStmt scenarios consume that fact. The three focused statement groups pass
25 checks; this does not replace the dated full-suite scan above.

The [field-function and square-inference repair](experience/problem_notes/field-preimage-and-power-2026-10-04.md)
passes a fresh scoped CLI gate of 378 Stmt checks and 175 basics, plus 46
relevant Rust tests. Its new tracers live with their Stmt/infer owners; this
is not a full release or independent-replay claim.

## Run

From the repository root:

```bash
cargo build --release
python3 examples/test_statements/run.py
cargo test --release --test test_statements
```

The Python runner checks process status and the single current CLI JSON
envelope (`success`, `statement_results`, and `session_error`). Rejections
must have the expected failure phase or parser/strict diagnostic, and setup
statements must succeed. The rollback scenario requires exactly
`[false, true, true]` for rejection, correction, and subsequent use.
Crashes, timeouts, launch errors, malformed JSON, and unexpected stderr fail
the suite; they cannot masquerade as a successful negative test.

The Rust integration test parses and executes the actual fixtures through
`Runtime::exec_stmt`, checks that each dedicated file contains its advertised
AST leaf, and exhaustively matches every statement family. It also checks all
11 `TemplateDefEnum` bodies, all 10 `Fact` shapes, nested induction cases, and
the actual values returned by `eval` (including an exact fraction and recursive
algorithm evaluation). An added AST variant requires updating coverage.
This test uses only successful fixtures; the CLI runner owns rejection and
rollback assertions through the production run boundary.

Focused checks and the gap-free gate:

```bash
python3 examples/test_statements/run.py --leaf HaveObjEqualStmt
python3 examples/test_statements/run.py --require-no-gaps
```

The ordinary runner prints every `KNOWN` gap and succeeds only when current
observations match all explicit expectations. **This does not close those
issues.** `--require-no-gaps` exits 1 while the recorded gaps remain. A gap
changing behavior also fails the ordinary runner, prompting review and removal
of its stale issue record. See the [issue index](bugs/README.md) for per-statement
folders containing exact reproductions, captured output, checked controls, and
repair acceptance commands. The index links the resolved trust-have display defect
D001 and its fresh-parser replay acceptance.

`--report <path>` saves the complete structured result; `--binary <path>` tests
another release binary. Neither option changes fixtures or expectations.

K003 uses the accepted explicit equality chain [`f(2) = f(2 - 1) = f(1) = 0`](boundaries/recursive-equation-explicit-chain.lit). It is recorded as a [current proof-search limitation](experience/problem_notes/K003-explicit-recursive-equation-chain.md), not an open bug.

K004 uses the user's [explicit arithmetic chain](boundaries/recursive-increment-explicit-chain.lit). K010's [original arithmetic enumeration](boundaries/finite-numeric-enumeration.lit) now succeeds using finite-carrier membership evidence. Both are ordinary successful coverage. [Focused acceptance](proof_journals/k004_k010_d001_acceptance.json) also records D001's output replay.

K005 now uses [enumeration plus explicit by-contra](boundaries/finite-negated-existence-by-contra.lit). Its [solution and controls](experience/problem_notes/K005-classified-negative-existence-contra.md) preserve the original conclusion. Remaining all-fact command work is listed [by statement](bugs/by_contra_stmt/limitations.md).

## First acceptance example

The new typed-equality fixture accepts and reuses a natural value:

```litex
have typed_n N = 1
typed_n = 1
typed_n $in N
```

Its negative fixture rejects `have k N = -1`. A separate scenario then corrects
the same name to `have k N = 1` and verifies `k = 1`, proving the failed
declaration did not reserve the name or publish a binding.

## Layout and trust boundaries

- Root `.lit` files: successful per-statement fixtures; `# case:` markers are
  both readable scenario labels and the independent runner's delimiters.
- `negative/`: inputs that must reject. Run them through `run.py`; a plain
  `litex -f` invocation is expected to exit 1.
- `boundaries/`: strict policy, selected-theorem syntax, and command/scope
  effects. Some boundaries deliberately accept current documented behavior.
- `bugs/<statement>/<issue>/`: unresolved reproductions, issue notes, and actual
  JSON output. Desired and observed results remain separate in `manifest.json`.
- `bugs/<statement>/limitations.md`: existing restrictions and policy boundaries;
  `bugs/tooling/` records CLI/documentation drift.
- `manifest.json`: leaf paths, payload names, scenario flags, and explicit
  expectations. Inventory audits detect missing, duplicate, or unlisted files.
- `proof_journals/`: authoring attempts, comparisons, final CLI results, and
  acceptance metadata. They are evidence, not additional test inputs.

Most scenarios use `-strict`. Trust statements, abstract predicates, and
explicit axiomatic interfaces are tested in their appropriate mode. The template
fixture includes one deliberately trusted `TemplateDefEnum::TrustHaveStmt`
scenario; only that isolated scenario and the combined template file use
non-strict mode. This is language-construct coverage, not proof debt inserted
to make another test pass. Zorn and choice fixtures make obligations explicit
inside conditional claims. User axioms run only in ordinary mode; strict mode
rejects their declarations, including nested and imported forms. Pure abstract
signatures and choice/regularity release remain explicitly asserted strict
boundaries.

The template trust bypass under `-strict` is a resolved rejection regression.
Conditional enumeration and binder-reference cases are ordinary boundaries;
Cartesian-domain enumeration remains explicitly unsupported.
Inference and membership lines retained after declarations are test assertions
of stored consequences. They deliberately exercise subsequent use.

The `Fact` fixture exercises all ten fact shapes. Unique existence uses a
checked witness before assertion; negated existence is asserted in a local
conditional context. It does not claim automatic proof search for every
logical shape. The bare K005 shortcut remains an expected-failure automatic-search boundary;
its explicit contradiction proof is ordinary successful regression coverage.

These files are independent test inputs, not a shared Litex module; there is
no `litex.config`, exported API, or dependency on the earlier `stmt_nodes`
fixtures at runtime. Use the manifest runner rather than treating every
recursive `.lit` file in this directory as a positive example.

## Coverage inventory

| Stmt leaf | Primary fixture | Positive scenarios | Negative scenarios |
| --- | --- | ---: | ---: |
| `Fact` | [fact.lit](fact.lit) | 4 | 4 |
| `TrustStmt` | [trust_stmt.lit](trust_stmt.lit) | 3 | 2 |
| `TrustHaveStmt` | [trust_have_stmt.lit](trust_have_stmt.lit) | 3 | 2 |
| `LetObjStmt` | [let_obj_stmt.lit](let_obj_stmt.lit) | 3 | 3 |
| `HaveObjInNonemptySetStmt` | [have_obj_in_nonempty_set_stmt.lit](have_obj_in_nonempty_set_stmt.lit) | 3 | 2 |
| `HaveObjEqualStmt` | [have_obj_equal_stmt.lit](have_obj_equal_stmt.lit) | 3 | 4 |
| `HaveObjByExistFactsStmt` | [have_obj_by_exist_facts_stmt.lit](have_obj_by_exist_facts_stmt.lit) | 3 | 2 |
| `ObtainObjFromExistFact` | [obtain_obj_from_exist_fact.lit](obtain_obj_from_exist_fact.lit) | 3 | 2 |
| `ObtainObjFromAtomicFact` | [obtain_obj_from_atomic_fact.lit](obtain_obj_from_atomic_fact.lit) | 3 | 2 |
| `HaveByPreimageStmt` | [have_by_preimage_stmt.lit](have_by_preimage_stmt.lit) | 3 | 2 |
| `HaveByReplacementAxiomStmt` | [have_by_replacement_axiom_stmt.lit](have_by_replacement_axiom_stmt.lit) | 3 | 2 |
| `HaveFnEqualStmt` | [have_fn_equal_stmt.lit](have_fn_equal_stmt.lit) | 3 | 3 |
| `HaveFnEqualCaseByCaseStmt` | [have_fn_equal_case_by_case_stmt.lit](have_fn_equal_case_by_case_stmt.lit) | 3 | 2 |
| `HaveFnByInducStmt` | [have_fn_by_induc_stmt.lit](have_fn_by_induc_stmt.lit) | 4 | 2 |
| `HaveFnByForallExistUniqueStmt` | [have_fn_by_forall_exist_unique_stmt.lit](have_fn_by_forall_exist_unique_stmt.lit) | 3 | 2 |
| `DefPropStmt` | [def_prop_stmt.lit](def_prop_stmt.lit) | 3 | 3 |
| `DefAbstractPropStmt` | [def_abstract_prop_stmt.lit](def_abstract_prop_stmt.lit) | 3 | 2 |
| `DefTemplateStmt` | [def_template_stmt.lit](def_template_stmt.lit) | 9 | 2 |
| `DefStructStmt` | [def_struct_stmt.lit](def_struct_stmt.lit) | 3 | 3 |
| `DefAlgoByCasesStmt` | [def_algo_by_cases_stmt.lit](def_algo_by_cases_stmt.lit) | 3 | 2 |
| `DefAlgoByInducStmt` | [def_algo_by_induc_stmt.lit](def_algo_by_induc_stmt.lit) | 5 | 2 |
| `DefThmStmt` | [def_thm_stmt.lit](def_thm_stmt.lit) | 3 | 2 |
| `AxiomStmt` | [axiom_stmt.lit](axiom_stmt.lit) | 3 | 2 |
| `DefStrategyStmt` | [def_strategy_stmt.lit](def_strategy_stmt.lit) | 4 | 3 |
| `ReleaseThmStmt` | [release_thm_stmt.lit](release_thm_stmt.lit) | 3 | 3 |
| `ReleaseStructDefStmt` | [release_struct_def_stmt.lit](release_struct_def_stmt.lit) | 3 | 2 |
| `ReleaseObjDefStmt` | [release_obj_def_stmt.lit](release_obj_def_stmt.lit) | 3 | 2 |
| `ExpandRangeStmt` | [expand_range_stmt.lit](expand_range_stmt.lit) | 3 | 2 |
| `ReleaseZornLemmaStmt` | [release_zorn_lemma_stmt.lit](release_zorn_lemma_stmt.lit) | 2 | 2 |
| `ReleaseAxiomOfChoiceStmt` | [release_axiom_of_choice_stmt.lit](release_axiom_of_choice_stmt.lit) | 3 | 2 |
| `ReleaseRegularityAxiomStmt` | [release_regularity_axiom_stmt.lit](release_regularity_axiom_stmt.lit) | 3 | 3 |
| `ByCasesStmt` | [by_cases_stmt.lit](by_cases_stmt.lit) | 4 | 2 |
| `ByContraStmt` | [by_contra_stmt.lit](by_contra_stmt.lit) | 6 | 4 |
| `ByEnumerateFiniteSetStmt` | [by_enumerate_finite_set_stmt.lit](by_enumerate_finite_set_stmt.lit) | 5 | 4 |
| `ByInducStmt` | [by_induc_stmt.lit](by_induc_stmt.lit) | 3 | 3 |
| `ByStrongInducStmt` | [by_strong_induc_stmt.lit](by_strong_induc_stmt.lit) | 3 | 3 |
| `ByForStmt` | [by_for_stmt.lit](by_for_stmt.lit) | 5 | 4 |
| `ByExtensionStmt` | [by_extension_stmt.lit](by_extension_stmt.lit) | 4 | 2 |
| `ByFnExtensionStmt` | [by_fn_extension_stmt.lit](by_fn_extension_stmt.lit) | 4 | 2 |
| `ByDefStmt` | [by_def_stmt.lit](by_def_stmt.lit) | 3 | 2 |
| `ByThmStmt` | [by_thm_stmt.lit](by_thm_stmt.lit) | 3 | 2 |
| `RegisterReflexivePropStmt` | [register_reflexive_prop_stmt.lit](register_reflexive_prop_stmt.lit) | 3 | 5 |
| `RegisterSymmetricPropStmt` | [register_symmetric_prop_stmt.lit](register_symmetric_prop_stmt.lit) | 3 | 5 |
| `RegisterTransitivePropStmt` | [register_transitive_prop_stmt.lit](register_transitive_prop_stmt.lit) | 3 | 5 |
| `WitnessExistFact` | [witness_exist_fact.lit](witness_exist_fact.lit) | 3 | 3 |
| `WitnessAtomicFact` | [witness_atomic_fact.lit](witness_atomic_fact.lit) | 3 | 3 |
| `WitnessNonemptySet` | [witness_nonempty_set.lit](witness_nonempty_set.lit) | 3 | 2 |
| `ClaimStmt` | [claim_stmt.lit](claim_stmt.lit) | 3 | 2 |
| `SketchStmt` | [sketch_stmt.lit](sketch_stmt.lit) | 3 | 2 |
| `EvalStmt` | [eval_stmt.lit](eval_stmt.lit) | 5 | 4 |

The added `release_cart_def_stmt.lit` covers the approved complete Cartesian-definition command and reuses its stored equality.

The added [release_tuple_def_stmt.lit](release_tuple_def_stmt.lit) covers the exact finite-sequence bridge for an individual tuple. Its four executable negative fixtures preserve infinite-domain, scalar, WD and body rejection; native controls also check coordinate bounds and rollback. See [2026-10-08 acceptance](../stmt_nodes/experience/problem_notes/release_tuple_def_2026-10-08.md).

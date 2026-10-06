# Litex Reference

## Status and reading model

Organization selected: **dictionary entries with mathematical task routes**.
This first dictionary edition has a reconciled inventory of **51 public
statement forms, 93 active object leaves, 20 builtin atomic families with their
negative forms, and two native certificate predicates**. Entries retain the
accepted sample format and have independently executed examples. The inventory
is the current native language surface, not every standard-library theorem or
every leaf rewrite rule in the kernel.

A useful Litex entry connects four things: the mathematical operation, the
conditions making it meaningful, the facts a statement leaves available, and
the explicit proof steps that consume those facts. The sample thread is a
reciprocal function: division requires a nonzero input; its function signature
must record that domain; membership supplies carrier information; later
algebra may need an explicit equality bridge.

Every unskipped `litex` fence below is self-contained and independently checked.
Negative fences are marked **Expected rejection** and skipped by the positive
Markdown collector; they are verified separately as rejection controls.
The [verification record](audits/reference-samples-2026-10-06.json) preserves
source, attempts, failure phases, commands, and deletion controls. Checked mathematics uses strict mode. The three entries explaining user
`trust`, `trust have`, and `axiom` have explicitly labelled ordinary-mode
assumption demonstrations and separate strict-mode rejection checks.

## Entry contract and coverage framework

| Entry type | What the reader can find in one place |
|---|---|
| Statement | Mathematical action; prerequisites; actual execution; stored/exported results; scope/boundary; checked example; source; related entries |
| Object | Meaning and spelling; exact WD/domain; common native properties; how to establish/use them; boundary; multiple uses; source; related entries |
| Atomic fact | Meaning and argument orientation; positive/negative domains; definitions and relationships; verification versus inference; examples and boundaries |

The S, O and F numbers are stable lookup identifiers. Related public spellings
share an entry when their mathematical contract is identical. Semantically
different modes have separate entries: arbitrary `have`, value `have`, and
specification `have` are not one undifferentiated command. Unique witnesses
have a separate statement entry even though they share an AST family.

The [machine inventory](audits/reference-inventory-2026-10-06.json) reconciles
all active AST leaves with parser support. Removed forms have a separate
compatibility section. Certificate predicates use C identifiers because their
truth is produced/consumed by native theorem interfaces rather than ordinary
user predicate definitions. Reserved theorem calls have a separate index.

Property lists are source-backed native families with their actual guards;
the checked examples show concrete supported uses. They do not promise that
every mathematically equivalent spelling or larger combination is discovered
automatically. Prefer the listed explicit interface when it carries quantified
or compound requirements.

### Binder and fact-shape guide

| Form | Meaning and important boundary | Primary route |
|---|---|---|
| `forall x S: ...` | A proposition for every member; its binder stays local and no nonemptiness assertion is implied | Bare fact, claim or theorem |
| `forall A set: ...` | A meta-level set parameter, not membership in a writable universal set | Typed binder |
| `finite_set` / `nonempty_set` binder category | Supplies the named predicate obligations, rather than a host carrier object | Typed binder |
| Premises followed by `=>:` | Local mathematical hypotheses used for the conclusions | Guarded universal/claim |
| `exist ... st {facts}` | At least one complete witness tuple | Witness; obtain for elimination |
| `exist! ... st {facts}` | Existence plus componentwise uniqueness of complete candidates | Unique witness and specification function |
| Flat `and` | All supported atomic components | Check/store components |
| `or` | At least one supported branch; neither branch is chosen merely by storing it | Prove a branch or use exhaustive cases |
| Equality/order chain | The adjacent steps and their supported transitive consequences | Explicit intermediate expressions |
| `forall ... <=>:` | Both directions under the common domain; a guard on one side does not guard the other | Two directional obligations |
| `not exist` / `not forall` | Quantified negation with the supported De Morgan/counterexample shape | Explicit contradiction/witness routes |

Fact nesting is bounded: existential and builder bodies are quantifier-free;
a direct quantified condition can be named by a real concrete `prop`.
Universal conclusions cannot contain an extra nested universal; use a single
compatible parameter header when that preserves the mathematical dependency.
Universal hypotheses, as in the Zorn interface, have their supported scoped
role. A bare universal body contains facts; proof commands belong in a proof
statement's body. The examples in the dictionaries show the active-binder form.

## Two lookup indexes

### I know the syntax

| Public form | Mathematical use | Entry |
|---|---|---|
| `have fn f(...) T = body` | Define a callable value by an expression | [S01](#s01-expression-defined-functions) |
| `a / b` | Divide scalars by a nonzero scalar | [O01](#o01-division) |
| `x $in S`, `not x $in S` | Assert membership or nonmembership | [F01](#f01-membership-and-nonmembership) |
| `claim` with an equality chain | Prove a goal through explicit algebraic steps | [P04](#p04-connect-division-and-multiplication-explicitly) |
| `witness $is_nonempty_set(S) from value` | Certify a set contains a concrete object | [P06](#p06-arbitrary-have-needs-nonemptiness) |

### I know the mathematics

| Mathematical intention | Route through the dictionary |
|---|---|
| Define the reciprocal on nonzero reals | [R01](#r01-define-and-use-a-reciprocal-function) → [S01](#s01-expression-defined-functions) → [O01](#o01-division) |
| Make `1 / x` meaningful | [O01 domain](#domain-and-well-definedness) → [P01](#p01-reflexivity-does-not-bypass-well-definedness) |
| Learn what follows from a carrier declaration | [F01 relationships](#relationships-with-other-facts) |
| Turn `a / b = c` into `a = c * b` | [P04](#p04-connect-division-and-multiplication-explicitly) |
| Use a function equation inside a product | [R01 proof](#prove-a-law-of-the-function) → [P05](#p05-a-function-equation-may-need-to-be-exposed-before-substitution) |
| Select an arbitrary member of a defined set | [P06](#p06-arbitrary-have-needs-nonemptiness) |

## Statement dictionary

| ID | Public form | Mathematical role | Example status |
|---|---|---|---|
| [S01](#s01-expression-defined-functions) | `have fn ... = body` | Expression-defined functions | checked |
| [S02](#s02-bare-factual-statements) | `fact` | Bare factual statements | checked |
| [S03](#s03-equality-aliases) | `let name = expression` | Equality aliases | checked |
| [S04](#s04-arbitrary-members) | `have x S` | Arbitrary members | checked |
| [S05](#s05-typed-values-given-by-equality) | `have x S = value` | Typed values given by equality | checked |
| [S06](#s06-members-satisfying-a-proved-specification) | `have x S: facts` | Members satisfying a proved specification | checked |
| [S07](#s07-extract-existential-witnesses) | `obtain names from exist ...` | Extract existential witnesses | checked |
| [S08](#s08-extract-witnesses-through-a-predicate) | `obtain names from $P(args)` | Extract witnesses through a predicate | checked |
| [S09](#s09-extract-function-preimages) | `have by fn_preimage: names from value $in fn_range(f)` | Extract function preimages | checked |
| [S10](#s10-replacement-images) | `have by replacement_axiom: Img from prop P, set A` | Replacement images | checked |
| [S11](#s11-piecewise-functions) | `have fn ... by cases:` | Piecewise functions | checked |
| [S12](#s12-functions-by-decreasing-integer-measure) | `have fn ... by induc n from lower:` | Functions by decreasing integer measure | checked |
| [S13](#s13-functions-from-unique-existence) | `have fn f by exist!:` | Functions from unique existence | checked |
| [S14](#s14-concrete-predicates) | `prop P(parameters): facts` | Concrete predicates | checked |
| [S15](#s15-abstract-predicate-signatures) | `abstract_prop P(parameters)` | Abstract predicate signatures | checked |
| [S16](#s16-structured-carriers) | `struct Name<optional parameters>:` | Structured carriers | checked |
| [S17](#s17-parameterized-declaration-families) | `template<parameters>:` | Parameterized declaration families | checked |
| [S18](#s18-named-theorems) | `thm name: ? goal` | Named theorems | checked |
| [S19](#s19-named-axioms) | `axiom name: ? goal` | Named axioms | assumption demonstration |
| [S20](#s20-reusable-proof-strategies) | `strategy name: ? forall ...` | Reusable proof strategies | checked |
| [S21](#s21-executable-functions-by-cases) | `algo ... by cases:` | Executable functions by cases | checked |
| [S22](#s22-executable-functions-by-induction) | `algo ... by induc measure from lower:` | Executable functions by induction | checked |
| [S23](#s23-explicitly-trusted-facts) | `trust: facts` | Explicitly trusted facts | assumption demonstration |
| [S24](#s24-trusted-witness-introduction) | `trust have names carriers: facts` | Trusted witness introduction | assumption demonstration |
| [S25](#s25-publish-theorem-conclusions) | `release thm name(arguments)` | Publish theorem conclusions | checked |
| [S26](#s26-select-one-theorem-consequence) | `by thm name(arguments) => atomic_fact` | Select one theorem consequence | checked |
| [S27](#s27-open-one-struct-definition-layer) | `release struct def expression` | Open one struct definition layer | checked |
| [S28](#s28-replay-an-object-definition) | `release obj def identifier` | Replay an object definition | checked |
| [S29](#s29-expand-finite-integer-membership) | `expand: value $in range(...)` | Expand finite integer membership | checked |
| [S30](#s30-regularity-release) | `release regularity_axiom(S)` | Regularity release | checked |
| [S31](#s31-choice-release) | `release axiom_of_choice: set F:` | Choice release | checked |
| [S32](#s32-zorn-release) | `release zorn_lemma: set S, prop P, prop U, prop M:` | Zorn release | checked |
| [S33](#s33-local-claims) | `claim: ? goal` | Local claims | checked |
| [S34](#s34-local-sketches) | `sketch: statements` | Local sketches | checked |
| [S35](#s35-existential-witnesses) | `witness exist ... from values` | Existential witnesses | checked |
| [S36](#s36-unique-existential-witnesses) | `witness exist! ... from values` | Unique existential witnesses | checked |
| [S37](#s37-witnesses-for-named-existential-properties) | `witness $P(args) from values` | Witnesses for named existential properties | checked |
| [S38](#s38-nonempty-set-witnesses) | `witness $is_nonempty_set(S) from value` | Nonempty-set witnesses | checked |
| [S39](#s39-proof-by-exhaustive-cases) | `by cases:` | Proof by exhaustive cases | checked |
| [S40](#s40-proof-by-contradiction) | `by contra:` | Proof by contradiction | checked |
| [S41](#s41-finite-set-enumeration) | `by enumerate finite_set:` | Finite-set enumeration | checked |
| [S42](#s42-ordinary-induction) | `by induc n from lower:` | Ordinary induction | checked |
| [S43](#s43-strong-induction) | `by strong_induc n from lower:` | Strong induction | checked |
| [S44](#s44-finite-range-iteration) | `by for:` | Finite range iteration | checked |
| [S45](#s45-set-extensionality) | `by extension A = B` | Set extensionality | checked |
| [S46](#s46-function-extensionality) | `by fn_extension f = g` | Function extensionality | checked |
| [S47](#s47-explicit-definition-folding) | `by def positive_fact` | Explicit definition folding | checked |
| [S48](#s48-register-reflexive-predicate-laws) | `register reflexive: ? forall ...` | Register reflexive predicate laws | checked |
| [S49](#s49-register-symmetric-predicate-laws) | `register symmetric: ? forall ...` | Register symmetric predicate laws | checked |
| [S50](#s50-register-transitive-predicate-laws) | `register transitive: ? forall ...` | Register transitive predicate laws | checked |
| [S51](#s51-exact-evaluation) | `eval expression` | Exact evaluation | checked |

### S01. Expression-defined functions

**Public form:** `have fn f(parameters: optional guards) T = body`.
This entry covers the expression-defined form. See S11 for cases, S12 for
induction, and S13 for the unique-existence construction.

#### Mathematical function

Introduce a mathematical function, its callable domain, and its defining
expression. The declaration also checks that the body lies in the written
return set for admissible inputs. It is a definition of a value that later
lines can call; a predicate about a value has a different role.

```litex
have fn successor(n N) N = n + 1
successor(2) = 3
successor $in fn(n N) N
```

The first line defines `successor`; the second uses the defining expression;
the third checks its function-space membership. `n` is a local function
parameter. It does not become a top-level object.

#### Parameters, domain, and return set

The parameter carrier says which values may be supplied. Guards further
restrict admissible inputs. The final carrier states where every output lies.
For division, the nonzero condition belongs to the callable domain:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
reciprocal(-2) = -1 / 2
```

This is a reciprocal on nonzero real inputs. `R` in the result position is a
return bound; it does not assert that the function can be called at every real.
The guard must also hold at each application.

Multiple parameters follow the same principle:

```litex
have fn divide(a, b R: b != 0) R = a / b
divide(6, 2) = 3
```

In current function signatures, the parameter carrier expressions and return
carrier cannot reference the signature's own parameter names. Guards and the
expression body can use those names. The examples here use fixed carriers.

#### Execution flow

For the ordinary nonempty input domains in these examples, the pipeline is:

1. Construct the anonymous function corresponding to the declaration.
2. Check parameter carrier objects, introduce local parameter names and their
   membership facts, and check the guards as local assumptions.
3. Check the return carrier and the expression body. In the reciprocal,
   checking `1 / x` consumes the local `x != 0` guard.
4. Verify the expression's membership in the return set. For example,
   `1 / x $in R` follows from real arithmetic closure after division WD.
5. Check the function-space object for the signature.
6. Occupy the new name and store its function-space membership and equality
   with the anonymous defining function, with ordinary inference.
7. Commit the successful statement's local transaction to the parent context.

The implementation also has an independently checked empty-complete-domain
case for the pointwise return obligation. Header, return-carrier, and body WD
still apply. The samples here do not exercise that case.

#### What success leaves available

For the guarded reciprocal, the stored mathematical interfaces are:

- Function-space membership: `reciprocal $in fn(x R: x != 0) R`.
- Equality with the anonymous function: `reciprocal = fn(x R: x != 0) R {1 / x}`.
- Callable applications satisfying the parameter and guard checks.
- Defining application equalities, as illustrated by `reciprocal(2) = 1 / 2`.

The defining equation can prove an application equality. It does not promise
that every larger expression is automatically rewritten everywhere; see
[P05](#p05-a-function-equation-may-need-to-be-exposed-before-substitution).

In the verified output, calls such as `reciprocal(2) = 1 / 2` use
`proof_method.type: object_definition`. Function-space membership is stored
rather than left as a conjecture.

#### Scope and failure

The function name becomes available in the surrounding scope. Parameters and
local WD assumptions stay inside their binder scope. The statement executes
in a temporary environment; failed execution does not merge that environment.

Writing a return set does not establish the return obligation.
**Expected rejection — phase `have_fn_equal`; the pointwise return bound fails:**

<!-- litex:skip-test -->
```litex
have fn wrong(x R) N = x
```

An arbitrary real is not necessarily natural. The rejected declaration has
not supplied a definition of a function from all reals to naturals. Choose the
actual mathematical domain and codomain rather than a convenient output label.

For the intended identity on reals, the return carrier is `R`:

```litex
have fn identity(x R) R = x
identity(1 / 2) = 1 / 2
```

**Evidence:** S01–S04 and D07–D08 in the verification record.
**Source:** [function statement executor](../src/execute/execute_have_fn_equal_stmt.rs),
[anonymous-function WD](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/binder.rs),
[statement transaction](../src/execute/exec_stmt.rs).

### S02. Bare factual statements

**Public form:** `fact`.

**Mathematical function.** Ask the checker to establish a proposition from the current mathematical context.

**Before execution.** The fact and every expression it contains must be well-defined; quantified facts introduce their own scoped binders and premises.

**Execution and result.** Check WD, then the fact-shaped verification route. On success store the fact and its applicable ordinary inferred consequences. A search miss commits no successful fact.

**Nearest boundary.** A failed assertion is not a proof of its negation. Proof commands belong in proof bodies, not in a bare universal conclusion list.

**Checked example.**

```litex
have x R = 2
x + 1 = 3
forall t R:
    t + 0 = t
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/exec_fact_stmt.rs); `S02` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership).

### S03. Equality aliases

**Public form:** `let name = expression`.

**Mathematical function.** Give an already meaningful value a fresh local name, including a callable value.

**Before execution.** The right-hand object must be WD and the name must be fresh in its scope.

**Execution and result.** Check the expression, occupy the name, and store the defining equality with inference. No carrier is explicitly declared by the syntax; applicable membership can be checked from the value.

**Nearest boundary.** An alias is not an additional hypothesis that its value satisfies an arbitrary property.

**Checked example.**

```litex
let a = 2
a + 1 = 3
let identity = fn(x R) R {x}
identity(4) = 4
```

**Source and evidence:** [implementation](../src/execute/execute_let_stmt.rs); `S03` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S04. Arbitrary members

**Public form:** `have x S`.

**Mathematical function.** Introduce an arbitrary member of a proved nonempty carrier.

**Before execution.** The carrier must be valid and nonempty; dependent parameter types must be available in declaration order.

**Execution and result.** Check the carrier/nonempty obligations, introduce the names, store their membership or parameter-type facts, and run ordinary inference. Direct struct-typed symbol bindings open one outer struct layer.

**Nearest boundary.** The declaration does not choose a specific numerical value. Nonempty selection is different from universal binding, which does not require a nonempty domain.

**Checked example.**

```litex
have n N
0 <= n
have x R*
x != 0
1 / x $in R
```

**Source and evidence:** [implementation](../src/execute/execute_have_obj_in_nonempty_set_stmt.rs); `S04` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S05. Typed values given by equality

**Public form:** `have x S = value`.

**Mathematical function.** Name a specific mathematical value while checking its carrier.

**Before execution.** The value must be WD and belong to the declared carrier; the fresh name cannot replace a failed membership proof.

**Execution and result.** Check the type/value requirements, occupy the name, then store membership and the defining equality, with ordinary inference.

**Nearest boundary.** An integer output carrier cannot be justified merely by writing Z next to a noninteger value.

**Checked example.**

```litex
have x R = 1 / 2
x $in R
x + 1 / 2 = 1
```

**Source and evidence:** [implementation](../src/execute/execute_have_obj_equal_stmt.rs); `S05` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S06. Members satisfying a proved specification

**Public form:** `have x S: facts`.

**Mathematical function.** Introduce witnesses satisfying a mathematical specification.

**Before execution.** The synthesized existential with exactly these carrier and body facts must verify; construct or prove it beforehand when the ordinary existential route does not close.

**Execution and result.** Build the existential goal, verify it, introduce fresh witnesses, and store their carrier and body facts. This checks existence; it does not simply assume the written body.

**Nearest boundary.** Use trust have only when an explicitly assumed witness is intended; ordinary have cannot skip existence.

**Checked example.**

```litex
witness exist x R st {x = 2} from 2
have a R:
    a = 2
a + 1 = 3
```

**Source and evidence:** [implementation](../src/execute/execute_have_obj_by_exist_facts_stmt.rs); `S06` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S07. Extract existential witnesses

**Public form:** `obtain names from exist ...`.

**Mathematical function.** Eliminate an established existential by naming its witnesses.

**Before execution.** The source existential must verify, witness count must match, and carriers may depend on earlier parameters. The exist! form additionally carries uniqueness.

**Execution and result.** Verify the source, instantiate its dependent types and quantifier-free body with fresh names, and store the resulting facts. The values are opaque witnesses, not guessed concrete numbers.

**Nearest boundary.** The existential is not itself a value; obtain gives names for use in later expressions. A local claim does not export its witness names.

**Checked example.**

```litex
witness exist! z R st {z = 1} from 1
obtain uniq from exist! z R st {z = 1}
uniq = 1
```

**Source and evidence:** [implementation](../src/execute/execute_obtain_obj_from_exist_fact_stmt.rs); `S07` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S35 Existential witnesses](#s35-existential-witnesses), [S36 Unique existential witnesses](#s36-unique-existential-witnesses).

### S08. Extract witnesses through a predicate

**Public form:** `obtain names from $P(args)`.

**Mathematical function.** Use a named existential property as the witness interface.

**Before execution.** The predicate instance must verify and its concrete definition must have the supported single positive existential clause. An abstract signature supplies no clause.

**Execution and result.** Resolve and instantiate the definition, project its existential, then perform the usual witness elimination and inference.

**Nearest boundary.** Extra definition clauses and other quantified shapes are not silently discarded. Use an explicit existential interface when the named form does not match.

**Checked example.**

```litex
prop has_copy(a R):
    exist x R st {x = a}

$has_copy(2)
obtain copy from $has_copy(2)
copy = 2
copy $in R
```

**Source and evidence:** [implementation](../src/execute/execute_obtain_obj_from_atomic_fact_stmt.rs); `S08` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S35 Existential witnesses](#s35-existential-witnesses), [S36 Unique existential witnesses](#s36-unique-existential-witnesses), [S07 Extract existential witnesses](#s07-extract-existential-witnesses).

### S09. Extract function preimages

**Public form:** `have by fn_preimage: names from value $in fn_range(f)`.

**Mathematical function.** Name input witnesses for an established image membership.

**Before execution.** The known image-membership source and callable signature must match; replacement images have their corresponding relation interface.

**Execution and result.** Verify the source membership, recover input domains, introduce opaque input witnesses, and store their types and application/relation equations.

**Nearest boundary.** Keep the source image constructor visible; an arbitrary equal set alias does not necessarily fit this structural statement interface.

**Checked example.**

```litex
have fn shift(x R) R = x + 1

shift(2) $in fn_range(shift)

have by fn_preimage: source from shift(2) $in fn_range(shift)

source $in R
shift(2) = shift(source)
```

**Source and evidence:** [implementation](../src/execute/execute_have_by_fn_preimage_stmt.rs); `S09` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S10. Replacement images

**Public form:** `have by replacement_axiom: Img from prop P, set A`.

**Mathematical function.** Construct a named image set by a functional relation, using Replacement.

**Before execution.** The source is a set, the predicate has the required binary relation shape, and the uniqueness condition on each source input is proved.

**Execution and result.** Check the relation/source/uniqueness contract and introduce a named replacement image with its definition-owned membership/preimage interface.

**Nearest boundary.** This is a foundational construction, not an anonymous replacement_image expression or permission to choose several unrelated outputs.

**Checked example.**

```litex
prop image_rel(x, y set):
    y = x

forall x {1, 2}, y, y2 set:
    $image_rel(x, y)
    $image_rel(x, y2)
    =>:
        y = y2

have by replacement_axiom: Img from prop image_rel, set {1, 2}

$is_set(Img)

release obj def Img
```

**Source and evidence:** [implementation](../src/execute/execute_have_by_replacement_axiom_stmt.rs); `S10` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S11. Piecewise functions

**Public form:** `have fn ... by cases:`.

**Mathematical function.** Define one function using exhaustive disjoint mathematical cases.

**Before execution.** Each guard is WD; coverage, pairwise disjointness, body WD and return membership must check under the corresponding case.

**Execution and result.** Check all case obligations before storing the function signature and guarded equations. These equations become available at calls whose case facts verify.

**Nearest boundary.** A case at zero alone does not define a total function on R. A formula in an unreachable branch still has its required WD checks.

**Checked example.**

```litex
have fn absolute(x R) R by cases:
    case x >= 0: x
    case x < 0: -x
absolute(-2) = 2
absolute(3) = 3
```

**Source and evidence:** [implementation](../src/execute/execute_have_fn_equal_case_by_case_stmt.rs); `S11` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S01 Expression-defined functions](#s01-expression-defined-functions), [O79 Function spaces](#o79-function-spaces), [O03 Function applications](#o03-function-applications).

### S12. Functions by decreasing integer measure

**Public form:** `have fn ... by induc n from lower:`.

**Mathematical function.** Define a recursive function whose recursive calls decrease an integer measure.

**Before execution.** The measure, lower bound, cases and return carrier are valid; every recursive call is in-domain and strictly smaller in the selected measure.

**Execution and result.** Check base and recursive cases with the controlled recursive signature, then store the callable interface and guarded defining equations.

**Nearest boundary.** A recursive call to the same or a larger measure is not licensed merely because it has the same output type.

**Checked example.**

```litex
have fn countdown(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: countdown(n - 1)
countdown(0) = 0
countdown(1) = countdown(0) = 0
```

**Source and evidence:** [implementation](../src/execute/execute_have_fn_by_induc_stmt.rs); `S12` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S01 Expression-defined functions](#s01-expression-defined-functions), [O79 Function spaces](#o79-function-spaces), [O03 Function applications](#o03-function-applications).

### S13. Functions from unique existence

**Public form:** `have fn f by exist!:`.

**Mathematical function.** Turn a proved input-to-unique-output specification into a callable mathematical function.

**Before execution.** The forall ... exist! statement and its function-space carrier must be WD and verified, including uniqueness for complete output tuples.

**Execution and result.** Store callable membership, the specification at f(input), and the corresponding uniqueness universal. This has no formula body to unfold into an evaluation equation.

**Nearest boundary.** A proof of existence alone is insufficient. Use the property interface at f(x), rather than inventing an expression defining its output.

**Checked example.**

```litex
prop F(x, y R):
    y = x
have A set = R
have B set = R

claim:
    ? forall x A:
        exist! y B st {$F(x, y)}
    witness exist! y B st {$F(x, y)} from x:
        by def $F(x, x)

have fn f by exist!:
    ? forall x A:
        exist! y B st {$F(x, y)}

forall x A:
    $F(x, f(x))
```

**Source and evidence:** [implementation](../src/execute/execute_have_fn_by_forall_exist_unique_stmt.rs); `S13` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S01 Expression-defined functions](#s01-expression-defined-functions), [O79 Function spaces](#o79-function-spaces), [O03 Function applications](#o03-function-applications).

### S14. Concrete predicates

**Public form:** `prop P(parameters): facts`.

**Mathematical function.** Define mathematical vocabulary by concrete defining clauses.

**Before execution.** Parameters and clauses must be WD. Earlier checked clauses may guard later partial expressions within definition WD.

**Execution and result.** Store the concrete definition. A verified positive instance can expose its clauses; by def checks the defining obligations explicitly. Definition alone does not assert every instance.

**Nearest boundary.** A predicate describes truth. Use have fn when later code needs a callable returned value.

**Checked example.**

```litex
prop is_positive(x R):
    x > 0
by def $is_positive(2)
$is_positive(2)
```

**Source and evidence:** [implementation](../src/execute/execute_def_prop_stmt/exec_def_prop_stmt.rs); `S14` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S15. Abstract predicate signatures

**Public form:** `abstract_prop P(parameters)`.

**Mathematical function.** Introduce a predicate signature for an external or uninterpreted property.

**Before execution.** The declaration and later calls must use the valid name and arity. No definition body or instance proof is supplied.

**Execution and result.** Store only the abstract predicate interface. Calls can be used as premises, or proved from actual assumptions/interfaces; there are no defining clauses to unfold.

**Nearest boundary.** An abstract_prop declaration is not an axiom proving $P(a). Strict mode allows the signature itself.

**Checked example.**

```litex
abstract_prop marked(x)

forall x R:
    $marked(x)
    =>:
        $marked(x)
```

**Source and evidence:** [implementation](../src/execute/execute_def_abstract_prop_stmt/exec_def_abstract_prop_stmt.rs); `S15` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S16. Structured carriers

**Public form:** `struct Name<optional parameters>:`.

**Mathematical function.** Define a product carrier with named fields and optional defining conditions.

**Before execution.** Field carriers and conditions are checked in declaration order. Membership in the resulting struct must satisfy its complete coordinate and property contract.

**Execution and result.** Store the definition-owned carrier, field schema and laws. Direct bindings x &Struct open one outer layer; other expressions can use explicit release struct def.

**Nearest boundary.** Declaring the carrier does not create an instance. Field WD is not a request to expose every nested struct law.

**Checked example.**

```litex
struct Point:
    x R
    y R

(1, 2) $in &Point

struct PosPoint:
    x R
    y R
    <=>:
        x > 0

(1, 2) $in &PosPoint
```

**Source and evidence:** [implementation](../src/execute/execute_def_struct_stmt/exec_def_struct_stmt.rs); `S16` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S17. Parameterized declaration families

**Public form:** `template<parameters>:`.

**Mathematical function.** Define a reusable family of supported ordinary definitions indexed by mathematical parameters.

**Before execution.** Template parameters, guards, allowed declaration shape, and each instantiated definition contract must check.

**Execution and result.** Store the family. The object spelling \Name<arguments> specializes it; a fully instantiated callable definition can then be applied. The ordinary declaration determines released facts.

**Nearest boundary.** Template parameters are not runtime function arguments. Instantiation must satisfy its own carrier and guard obligations.

**Checked example.**

```litex
template<S set>:
    have carrier_copy set = S

\carrier_copy<R> = R
```

**Source and evidence:** [implementation](../src/execute/execute_def_template_stmt/exec_def_template_stmt.rs); `S17` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S18. Named theorems

**Public form:** `thm name: ? goal`.

**Mathematical function.** Give a proved result a reusable named mathematical interface.

**Before execution.** The goal is WD in the existing context. Its active binders and premises provide the local proof scope; every conclusion must verify.

**Execution and result.** Run the proof and store the theorem interface. Universal theorem facts are reusable by ordinary matching as well as explicit theorem calls. A body may be empty when it already closes.

**Nearest boundary.** A later declaration in the proof body cannot make an earlier undefined goal WD. Helpers remain local.

**Checked example.**

```litex
thm add_zero:
    ? forall x R:
        x + 0 = x
release thm add_zero(2)
```

**Source and evidence:** [implementation](../src/execute/execute_def_thm_stmt/exec_def_thm_stmt.rs); `S18` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S33 Local claims](#s33-local-claims), [S34 Local sketches](#s34-local-sketches).

### S19. Named axioms

**Public form:** `axiom name: ? goal`.

**Mathematical function.** Name an explicitly assumed proposition for reuse.

**Before execution.** The interface and its expressions must be WD. Truth is assumed, not proved; strict mode rejects the declaration.

**Execution and result.** Store the named assumed interface and applicable universal information with its trust boundary. Calls still check their arguments and premises.

**Nearest boundary.** A successful ordinary run containing an axiom is not a trust-free proof of that axiom.

**Assumption demonstration.** Checked in ordinary mode; this is not a trust-free proof. Strict mode rejects the assumed declaration.

```litex
axiom background:
    ? forall x R:
        x = x
release thm background(2)
```

**Source and evidence:** [implementation](../src/execute/execute_axiom_stmt/exec_axiom_stmt.rs); `S19` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S33 Local claims](#s33-local-claims), [S34 Local sketches](#s34-local-sketches), [S18 Named theorems](#s18-named-theorems).

### S20. Reusable proof strategies

**Public form:** `strategy name: ? forall ...`.

**Mathematical function.** Prove a reusable pattern for the dedicated non-equality atomic strategy route.

**Before execution.** The goal is WD and the local proof establishes its conclusions; the current parser/executor permits the documented theorem-like proof body.

**Execution and result.** Store a strategy definition. Later applicable non-equality atomics can use known_strategy; the result is not injected as an ordinary ambient known-forall theorem.

**Nearest boundary.** There is no use/stop activation state. A strategy is not a global arbitrary goal-search program.

**Checked example.**

```litex
prop is_one(x R):
    x = 1

strategy use_is_one:
    ? forall x R:
        x = 1
        =>:
            $is_one(x)
    $is_one(x)

have a R = 1
$is_one(a)
```

**Source and evidence:** [implementation](../src/execute/execute_def_strategy_stmt/exec_def_strategy_stmt.rs); `S20` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S21. Executable functions by cases

**Public form:** `algo ... by cases:`.

**Mathematical function.** Define a checked piecewise function together with an executable presentation for eval.

**Before execution.** The same coverage, disjointness, WD and return obligations as the piecewise function apply.

**Execution and result.** Define the callable function and store the executable cases. eval computes through this presentation and checks executed defining equations.

**Nearest boundary.** An algorithm declaration does not waive mathematical domain or coverage requirements.

**Checked example.**

```litex
algo nonzero_flag(x R) R by cases:
    case x = 0: 0
    case x != 0: 1
eval nonzero_flag(2)
```

**Source and evidence:** [implementation](../src/execute/execute_def_algo_by_cases_stmt/exec_def_algo_by_cases_stmt.rs); `S21` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S01 Expression-defined functions](#s01-expression-defined-functions), [O79 Function spaces](#o79-function-spaces), [O03 Function applications](#o03-function-applications).

### S22. Executable functions by induction

**Public form:** `algo ... by induc measure from lower:`.

**Mathematical function.** Define a decreasing recursive function with an executable presentation.

**Before execution.** The induction-function obligations hold, including in-domain decreasing recursive calls and result membership.

**Execution and result.** Store the checked recursive function and executable algorithm. Exact eval checks the equations for the path actually executed.

**Nearest boundary.** Execution is not an independent proof of arbitrary facts about all inputs.

**Checked example.**

```litex
algo countdown(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: countdown(n - 1)
eval countdown(2)
```

**Source and evidence:** [implementation](../src/execute/execute_def_algo_by_induc_stmt/exec_def_algo_by_induc_stmt.rs); `S22` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S01 Expression-defined functions](#s01-expression-defined-functions), [O79 Function spaces](#o79-function-spaces), [O03 Function applications](#o03-function-applications).

### S23. Explicitly trusted facts

**Public form:** `trust: facts`.

**Mathematical function.** Record deliberately assumed facts.

**Before execution.** All expressions and fact signatures must be WD; strict mode rejects user trust.

**Execution and result.** Skip truth search, then store the trusted facts with inference. This cannot repair an ill-defined expression such as division by zero.

**Nearest boundary.** Trust is a visible assumption boundary, not a proof technique that establishes truth.

**Assumption demonstration.** Checked in ordinary mode; this is not a trust-free proof. Strict mode rejects the assumed declaration.

```litex
trust:
    7 = 7
7 = 7
```

**Source and evidence:** [implementation](../src/execute/execute_unsafe_stmt/exec_trust_stmt.rs); `S23` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S24. Trusted witness introduction

**Public form:** `trust have names carriers: facts`.

**Mathematical function.** Introduce objects and assume their specified facts without proving the matching existential.

**Before execution.** Parameter types, names and body expressions remain checked for WD. Strict mode rejects the statement.

**Execution and result.** Introduce typed names and store trusted body facts in one transaction. Subsequent proof steps are relative to these assumptions.

**Nearest boundary.** This differs from ordinary specification-have, whose existence must be proved.

**Assumption demonstration.** Checked in ordinary mode; this is not a trust-free proof. Strict mode rejects the assumed declaration.

```litex
trust have denominator R:
    denominator != 0

1 / denominator = 1 / denominator
```

**Source and evidence:** [implementation](../src/execute/execute_unsafe_stmt/exec_trust_have_stmt.rs); `S24` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S25. Publish theorem conclusions

**Public form:** `release thm name(arguments)`.

**Mathematical function.** Instantiate a reusable theorem and publish all its conclusions.

**Before execution.** The theorem exists, its argument syntax matches its goal shape, and all parameter domains and instantiated premises verify.

**Execution and result.** Instantiate and check the call, then store every resulting conclusion and its inference. Root forall theorems require parentheses even with no parameters; ordinary theorem facts use a bare name.

**Nearest boundary.** The form has no selection arrow or proof body. Bare by thm is supported as the unselected compatibility spelling.

**Checked example.**

```litex
thm zero_sides:
    ? forall x R:
        x + 0 = x
        0 + x = x
release thm zero_sides(2)
2 + 0 = 2
0 + 2 = 2
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_thm_stmt.rs); `S25` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S26. Select one theorem consequence

**Public form:** `by thm name(arguments) => atomic_fact`.

**Mathematical function.** Use a theorem instance to prove one requested atomic consequence.

**Before execution.** Arguments, domains and premises verify; the requested target is a supported single atomic fact.

**Execution and result.** Check the selected fact in the theorem-instance context, then publish that selection with inference. The public effect differs from releasing all conclusions.

**Nearest boundary.** An existential, universal, conjunction or chain is not a selectable atomic target; release the complete result when that shape is needed.

**Checked example.**

```litex
thm add_zero:
    ? forall x R:
        x + 0 = x
by thm add_zero(2) => 2 + 0 = 2
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_thm_stmt.rs); `S26` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S27. Open one struct definition layer

**Public form:** `release struct def expression`.

**Mathematical function.** Expose the tuple/coordinate bridges, carriers and laws of a selected struct view.

**Before execution.** The expression has a definition-owned struct view and its membership in that carrier verifies.

**Execution and result.** Resolve the selected declaration, instantiate and store exactly one outer layer of structural bridges, field carriers and laws.

**Nearest boundary.** Opening an outer struct does not recursively open every struct-valued field. Call release on the nested expression when its laws are needed.

**Checked example.**

```litex
struct Coordinates:
    x R
    y R
    <=>:
        x = 0

struct TaggedPoint:
    point &Coordinates
    tag N

claim:
    ? forall p &TaggedPoint:
        p.point.x = 0
    release struct def p.point
```

**Source and evidence:** [implementation](../src/execute/release_one_struct_layer.rs); `S27` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S28. Replay an object definition

**Public form:** `release obj def identifier`.

**Mathematical function.** Expose the stored mathematical interfaces belonging to an identifier definition.

**Before execution.** The source is a supported stored identifier definition, not an arbitrary object expression or a binder-only ParamType.

**Execution and result.** Re-store the definition-owned type, equality, body or function facts using the written identifier spelling. Unique-existence functions replay membership, property and uniqueness.

**Nearest boundary.** This does not discover a new theorem or erase the original definition obligations.

**Checked example.**

```litex
have fn identity(x R) R = x
release obj def identity
identity(2) = 2
```

**Source and evidence:** [implementation](../src/execute/execute_release_obj_def_stmt/exec_release_obj_def_stmt.rs); `S28` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S29. Expand finite integer membership

**Public form:** `expand: value $in range(...)`.

**Mathematical function.** Turn a known finite integer-range membership into equality alternatives.

**Before execution.** The membership verifies and the range/closed-range has the supported concrete enumerable shape.

**Execution and result.** Enumerate the range values and store a disjunction value = first or ... . This exposes cases without choosing one of them.

**Nearest boundary.** Expansion is not proof that an arbitrary object lies in the range. The closed upper endpoint differs from range’s excluded endpoint.

**Checked example.**

```litex
claim:
    ? forall x range(1, 3):
        x = 1 or x = 2
    expand: x $in range(1, 3)
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_expand_range_stmt.rs); `S29` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S30. Regularity release

**Public form:** `release regularity_axiom(S)`.

**Mathematical function.** Apply the fixed set-theoretic Regularity foundation through its checked release interface.

**Before execution.** The displayed set and nonemptiness obligations verify.

**Execution and result.** Check the inputs and expose the foundational conclusion for the given set. This named release is allowed by current strict mode.

**Nearest boundary.** Passing strict mode does not mean the foundation itself was derived without foundational assumptions.

**Checked example.**

```litex
release regularity_axiom({1})
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_regularity_axiom_stmt.rs); `S30` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S31. Choice release

**Public form:** `release axiom_of_choice: set F:`.

**Mathematical function.** Obtain a choice-function existence fact for a family of nonempty sets.

**Before execution.** F is a set and every A in F has a verified nonemptiness fact; the body proves these obligations in the caller context.

**Execution and result.** Store the existential choice-function fact with the appropriate function-space and atomic choice specification. Witness names require a later obtain.

**Nearest boundary.** Axiom of Choice does not establish nonemptiness of the family members; it uses it as an input. This is fixed foundational support.

**Checked example.**

```litex
claim:
    ? forall F set:
        forall A F:
            $is_nonempty_set(A)
        =>:
            exist f fn(A F) family_union(F) st {$is_choice_function_for(F, F, fn(B F) F {B}, f)}
    release axiom_of_choice: set F:
        forall A F:
            $is_nonempty_set(A)
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_axiom_of_choice_stmt.rs); `S31` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S32. Zorn release

**Public form:** `release zorn_lemma: set S, prop P, prop U, prop M:`.

**Mathematical function.** Use Zorn’s Lemma to establish existence of a maximal element.

**Before execution.** The exact named upper-bound/maximality definitions, nonempty poset, partial-order laws and chain-upper-bound condition must check.

**Execution and result.** Resolve the definitions, verify the semantic interface and all hypotheses, then store exist m S st {$M(m)}. The relation and supplied predicate definitions are part of the checked contract.

**Nearest boundary.** The theorem cannot replace a missing chain bound or an arbitrary predicate merely named maximal. The foundation is explicit.

**Checked example.**

```litex
have S set
abstract_prop leq(x, y)
prop upper_bound(c power_set(S), u S):
    forall x c:
        $leq(x, u)
prop maximal(m S):
    forall x S:
        $leq(m, x)
        =>:
            x = m

claim:
    ? forall:
        $is_nonempty_set(S)
        forall x S:
            $leq(x, x)
        forall x, y, z S:
            $leq(x, y)
            $leq(y, z)
            =>:
                $leq(x, z)
        forall x, y S:
            $leq(x, y)
            $leq(y, x)
            =>:
                x = y
        forall c power_set(S):
            forall x, y c:
                $leq(x, y) or $leq(y, x)
            =>:
                exist u S st {$upper_bound(c, u)}
        =>:
            exist m S st {$maximal(m)}
    release zorn_lemma: set S, prop leq, prop upper_bound, prop maximal:
        $is_nonempty_set(S)
        forall x S:
            $leq(x, x)
        forall x, y, z S:
            $leq(x, y)
            $leq(y, z)
            =>:
                $leq(x, z)
        forall x, y S:
            $leq(x, y)
            $leq(y, x)
            =>:
                x = y
        forall c power_set(S):
            forall x, y c:
                $leq(x, y) or $leq(y, x)
            =>:
                exist u S st {$upper_bound(c, u)}
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_zorn_lemma_stmt.rs); `S32` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S33. Local claims

**Public form:** `claim: ? goal`.

**Mathematical function.** Prove and export one target while keeping helper definitions and witnesses local.

**Before execution.** The target is WD in the existing context, before its proof-body declarations. Every proof statement and final goal must verify.

**Execution and result.** Introduce the goal’s local binders and premises, execute the proof body, verify the target, and export the target only.

**Nearest boundary.** A successfully introduced local witness or function does not escape the claim merely because the target succeeded.

**Checked example.**

```litex
claim:
    ? 3 = 3
    have local R = 3
    local = 3
3 = 3
```

**Source and evidence:** [implementation](../src/execute/execute_proof_block_stmt/exec_claim_stmt.rs); `S33` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S34 Local sketches](#s34-local-sketches), [S18 Named theorems](#s18-named-theorems).

### S34. Local sketches

**Public form:** `sketch: statements`.

**Mathematical function.** Check a small development in a discarded lexical scope.

**Before execution.** Every contained statement must succeed; a failed child fails the sketch.

**Execution and result.** Execute the local statements and discard the sketch environment afterwards. No contained name or fact is exported.

**Nearest boundary.** A sketch’s success is not a declaration of a reusable outside theorem.

**Checked example.**

```litex
sketch:
    have fn identity(x R) R = x
    identity(2) = 2
1 = 1
```

**Source and evidence:** [implementation](../src/execute/execute_proof_block_stmt/exec_sketch_stmt.rs); `S34` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S33 Local claims](#s33-local-claims), [S18 Named theorems](#s18-named-theorems).

### S35. Existential witnesses

**Public form:** `witness exist ... from values`.

**Mathematical function.** Prove an existential by giving concrete witnesses.

**Before execution.** Witness count, dependent carriers and expression WD check; the substituted body must verify, optionally using local proof steps.

**Execution and result.** Substitute the supplied values, check each obligation, and store the exact existential fact. Its bound names and proof helpers stay local.

**Nearest boundary.** Providing a value does not establish an unrelated body condition, nor does it make the existential binder globally usable.

**Checked example.**

```litex
witness exist x R st {x = 2} from 2
obtain a from exist x R st {x = 2}
a = 2
```

**Source and evidence:** [implementation](../src/execute/execute_witness_stmt/exec_witness_exist_fact.rs); `S35` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S36 Unique existential witnesses](#s36-unique-existential-witnesses), [S07 Extract existential witnesses](#s07-extract-existential-witnesses).

### S36. Unique existential witnesses

**Public form:** `witness exist! ... from values`.

**Mathematical function.** Prove existence and uniqueness of a complete witness tuple.

**Before execution.** All ordinary witness checks apply; the generated two-candidate uniqueness universal must also verify.

**Execution and result.** Store the unique existential and its applicable uniqueness information after checking both existence and uniqueness.

**Nearest boundary.** One positive real witness is not a proof that there is exactly one positive real.

**Checked example.**

```litex
witness exist! x R st {x = 2} from 2
obtain a from exist! x R st {x = 2}
a = 2
```

**Source and evidence:** [implementation](../src/execute/execute_witness_stmt/exec_witness_exist_fact.rs); `S36` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S35 Existential witnesses](#s35-existential-witnesses), [S07 Extract existential witnesses](#s07-extract-existential-witnesses).

### S37. Witnesses for named existential properties

**Public form:** `witness $P(args) from values`.

**Mathematical function.** Prove a supported concrete existential predicate through its witness interface.

**Before execution.** Arguments have their declared types and the definition has the supported single positive ordinary existential clause.

**Execution and result.** Check the projected existential witnesses and publish the predicate with ordinary definition inference.

**Nearest boundary.** For unique existence use witness exist! followed by explicit definition folding; extra clauses are not silently omitted.

**Checked example.**

```litex
prop has_copy(a R):
    exist x R st {x = a}
witness $has_copy(2) from 2
```

**Source and evidence:** [implementation](../src/execute/execute_witness_stmt/exec_witness_atomic_fact.rs); `S37` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S35 Existential witnesses](#s35-existential-witnesses), [S36 Unique existential witnesses](#s36-unique-existential-witnesses), [S07 Extract existential witnesses](#s07-extract-existential-witnesses).

### S38. Nonempty-set witnesses

**Public form:** `witness $is_nonempty_set(S) from value`.

**Mathematical function.** Prove that a set contains at least one element.

**Before execution.** The proposed object is WD and its membership in S verifies.

**Execution and result.** Check the membership in the optional local proof scope, then publish nonemptiness. This can license a later arbitrary have.

**Nearest boundary.** A value outside S cannot prove nonemptiness; a definition of S alone may not provide a witness route.

**Checked example.**

```litex
witness $is_nonempty_set({t R: t > 0}) from 1
have a {t R: t > 0}
a > 0
```

**Source and evidence:** [implementation](../src/execute/execute_witness_stmt/exec_witness_nonempty_set.rs); `S38` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S35 Existential witnesses](#s35-existential-witnesses), [S36 Unique existential witnesses](#s36-unique-existential-witnesses), [S07 Extract existential witnesses](#s07-extract-existential-witnesses).

### S39. Proof by exhaustive cases

**Public form:** `by cases:`.

**Mathematical function.** Prove a target in each branch of an established exhaustive case split.

**Before execution.** The case disjunction and all branch facts are supported and verify; every branch closes the target or reaches a checked contradiction.

**Execution and result.** Create local branch scopes, assume their case facts, check their proof bodies, and publish the target only after all branches succeed.

**Nearest boundary.** A convenient but nonexhaustive list of cases does not prove a universal conclusion.

**Checked example.**

```litex
by cases:
    ? 1 = 1
    case 1 = 1
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_cases_stmt.rs); `S39` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S40. Proof by contradiction

**Public form:** `by contra:`.

**Mathematical function.** Prove a supported goal by assuming its negation and deriving a contradiction.

**Before execution.** The target and generated negation are WD; impossible must certify an actual contradictory fact in the local context.

**Execution and result.** Open the negated-goal scope, execute the proof, verify the explicit contradiction, and store the requested target.

**Nearest boundary.** A bare unsupported impossible assertion is not a contradiction certificate. Negating a compound goal follows its supported fact shape.

**Checked example.**

```litex
by contra:
    ? 1 = 1
    impossible 1 != 1
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_contra_stmt.rs); `S40` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S41. Finite-set enumeration

**Public form:** `by enumerate finite_set:`.

**Mathematical function.** Prove a universal by checking every element of its finite displayed domains.

**Before execution.** The exact domains are concretely enumerable; each instantiated premise and conclusion has the supported shape.

**Execution and result.** Instantiate each domain combination, assume matching premises, execute the per-case proof, and publish the universal when all cases close.

**Nearest boundary.** A merely known finite set is not necessarily a displayed enumeration. Proof commands belong in this proof body, not the bare forall’s fact list.

**Checked example.**

```litex
by enumerate finite_set:
    ? forall x {1, 2}:
        x < 3
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_enumerate_finite_set_stmt.rs); `S41` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S42. Ordinary induction

**Public form:** `by induc n from lower:`.

**Mathematical function.** Prove a supported discrete universal by a base case and one-step induction.

**Before execution.** The active parameter, carrier, lower bound, hypotheses and invariant match the induction interface.

**Execution and result.** Check the base and inductive successor obligations in scoped contexts, then store the resulting universal.

**Nearest boundary.** The induction binder is part of the proof interface. A differently named mirror universal is not the original active goal.

**Checked example.**

```litex
by induc n from 0:
    ? n = n
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_induc_stmt.rs); `S42` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S43. Strong induction

**Public form:** `by strong_induc n from lower:`.

**Mathematical function.** Use the invariant for all smaller admissible indices to prove the current index.

**Before execution.** The measure, bound and supported discrete goal shape check; the strong hypothesis is limited to smaller in-domain indices.

**Execution and result.** Check the base and strong inductive obligations, then publish the universal result.

**Nearest boundary.** The hypothesis does not include the current index or an out-of-domain smaller value.

**Checked example.**

```litex
by strong_induc m from 0:
    ? m = m
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_induc_stmt.rs); `S43` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S44. Finite range iteration

**Public form:** `by for:`.

**Mathematical function.** Prove a universal over supported finite integer ranges or finite Cartesian domains.

**Before execution.** The domain is a supported finite iterable shape and all generated conditional goals are WD.

**Execution and result.** Enumerate the supported domain, execute local proof steps for each active assignment, and store the original universal.

**Nearest boundary.** This is not an arbitrary-set loop or a general-purpose programming for statement.

**Checked example.**

```litex
by for:
    ? forall n range(0, 3):
        n < 3
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_for_stmt.rs); `S44` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S45. Set extensionality

**Public form:** `by extension A = B`.

**Mathematical function.** Prove two sets equal by both membership directions.

**Before execution.** Both objects are WD and the two subset obligations verify; the block form may establish needed intermediates.

**Execution and result.** Check A subset B and B subset A, then store ordinary equality with extensionality evidence.

**Nearest boundary.** One inclusion is insufficient. Use function extensionality when proving callable equality through complete input domains.

**Checked example.**

```litex
by extension intersect(R, R) = R
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_extension_stmt.rs); `S45` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S46. Function extensionality

**Public form:** `by fn_extension f = g`.

**Mathematical function.** Prove functions equal from equal complete input domains and pointwise agreement.

**Before execution.** Both callable interfaces are established, complete domains agree, and values agree at every admissible input.

**Execution and result.** Check domain and pointwise obligations, then store ordinary equality f = g for later congruence.

**Nearest boundary.** Agreement at one input or equality of a codomain does not establish function equality. Local agreement belongs in a forall.

**Checked example.**

```litex
have fn f(x R) R = x
have fn g(x R) R = x
by fn_extension f = g

have fn add1(x R, y R) R = x + y
have fn add2(a R, b R) R = a + b
by fn_extension:
    ? add1 = add2
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_fn_extension_stmt.rs); `S46` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S47. Explicit definition folding

**Public form:** `by def positive_fact`.

**Mathematical function.** Prove a concrete user or builtin predicate by its exact defining obligations.

**Before execution.** The target is a supported positive definitional fact and every instantiated clause verifies.

**Execution and result.** Resolve the concrete definition, check all clauses, and store the target with explicit definition provenance.

**Nearest boundary.** Closed truth and an explicit definition proof can have different routes. For example prime(5) computes directly, but by def prime(5) still requires its trial-divisor universal.

**Checked example.**

```litex
prop is_zero(x R):
    x = 0
by def $is_zero(0)
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/exec_by_def_stmt.rs); `S47` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S48. Register reflexive predicate laws

**Public form:** `register reflexive: ? forall ...`.

**Mathematical function.** Register a proved reflexive law for a concrete binary predicate.

**Before execution.** The exact binary-predicate forall shape matches, the concrete predicate exists, and the universal law verifies.

**Execution and result.** Check the shape and predicate arity, verify the law in a local scope, then store the reusable rewrite-property route.

**Nearest boundary.** There is one shaped goal and no indented proof body. Registration cannot assume an unproved law or attach this interface to an arbitrary arity.

**Checked example.**

```litex
prop same(x set, y set):
    x = y

register reflexive:
    ? forall x set:
        $same(x, x)

have a set
$same(a, a)
```

**Source and evidence:** [implementation](../src/execute/execute_register_stmt/exec_register_reflexive_prop_stmt.rs); `S48` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S49. Register symmetric predicate laws

**Public form:** `register symmetric: ? forall ...`.

**Mathematical function.** Register a proved symmetric law for a concrete binary predicate.

**Before execution.** The exact binary-predicate forall shape matches, the concrete predicate exists, and the universal law verifies.

**Execution and result.** Check the shape and predicate arity, verify the law in a local scope, then store the reusable rewrite-property route.

**Nearest boundary.** There is one shaped goal and no indented proof body. Registration cannot assume an unproved law or attach this interface to an arbitrary arity.

**Checked example.**

```litex
prop same(x set, y set):
    x = y

register symmetric:
    ? forall x, y set:
        $same(x, y)
        =>:
            $same(y, x)

forall a, b set:
    $same(a, b)
    =>:
        $same(b, a)
```

**Source and evidence:** [implementation](../src/execute/execute_register_stmt/exec_register_symmetric_prop_stmt.rs); `S49` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S50. Register transitive predicate laws

**Public form:** `register transitive: ? forall ...`.

**Mathematical function.** Register a proved transitive law for a concrete binary predicate.

**Before execution.** The exact binary-predicate forall shape matches, the concrete predicate exists, and the universal law verifies.

**Execution and result.** Check the shape and predicate arity, verify the law in a local scope, then store the reusable rewrite-property route.

**Nearest boundary.** There is one shaped goal and no indented proof body. Registration cannot assume an unproved law or attach this interface to an arbitrary arity.

**Checked example.**

```litex
prop same(x set, y set):
    x = y

register transitive:
    ? forall x, y, z set:
        $same(x, y)
        $same(y, z)
        =>:
            $same(x, z)
```

**Source and evidence:** [implementation](../src/execute/execute_register_stmt/exec_register_transitive_prop_stmt.rs); `S50` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

### S51. Exact evaluation

**Public form:** `eval expression`.

**Mathematical function.** Compute a supported closed expression or algorithm call and record its result equality.

**Before execution.** Source/result expressions are WD; the exact computation and every executed algorithm defining equation must check.

**Execution and result.** Compute the value, verify the computation evidence, display the result, and store expression = value in the current scope.

**Nearest boundary.** A failed or out-of-domain computation commits no result. eval is not a proof-search command for arbitrary symbolic goals.

**Checked example.**

```litex
eval 2 + 3
2 + 3 = 5
```

**Source and evidence:** [implementation](../src/execute/execute_eval_stmt/exec_eval_stmt.rs); `S51` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements).

## Object dictionary

| ID | Public form | Mathematical role | Example status |
|---|---|---|---|
| [O01](#o01-division) | `a / b` | Division | checked |
| [O02](#o02-names-and-qualified-references) | `name; export::name; module::export::name; module:::name` | Names and qualified references | checked |
| [O03](#o03-function-applications) | `f(arguments)` | Function applications | checked |
| [O04](#o04-exact-numeric-literals) | `integer or decimal literal` | Exact numeric literals | checked |
| [O05](#o05-imaginary-unit) | `i` | Imaginary unit | checked |
| [O06](#o06-eulers-number) | `e` | Euler’s number | checked |
| [O07](#o07-pi) | `pi` | Pi | checked |
| [O08](#o08-natural-numbers-including-zero-n) | `N` | Natural numbers including zero: N | checked |
| [O09](#o09-positive-natural-numbers-n+) | `N+; Z+` | Positive natural numbers: N+ | checked |
| [O10](#o10-integers-z) | `Z` | Integers: Z | checked |
| [O11](#o11-rational-numbers-q) | `Q` | Rational numbers: Q | checked |
| [O12](#o12-real-numbers-r) | `R` | Real numbers: R | checked |
| [O13](#o13-complex-numbers-c) | `C` | Complex numbers: C | checked |
| [O14](#o14-positive-rationals-q+) | `Q+` | Positive rationals: Q+ | checked |
| [O15](#o15-positive-reals-r+) | `R+` | Positive reals: R+ | checked |
| [O16](#o16-negative-rationals-q-) | `Q-` | Negative rationals: Q- | checked |
| [O17](#o17-negative-integers-z-) | `Z-` | Negative integers: Z- | checked |
| [O18](#o18-negative-reals-r-) | `R-` | Negative reals: R- | checked |
| [O19](#o19-nonzero-rationals-q) | `Q*` | Nonzero rationals: Q* | checked |
| [O20](#o20-nonzero-integers-z) | `Z*` | Nonzero integers: Z* | checked |
| [O21](#o21-nonzero-reals-r) | `R*` | Nonzero reals: R* | checked |
| [O22](#o22-nonzero-complexes-c) | `C*` | Nonzero complexes: C* | checked |
| [O23](#o23-addition) | `a + b` | Addition | checked |
| [O24](#o24-subtraction) | `a - b` | Subtraction | checked |
| [O25](#o25-additive-inverse) | `-a` | Additive inverse | checked |
| [O26](#o26-multiplication) | `a * b` | Multiplication | checked |
| [O27](#o27-powers) | `a^b` | Powers | checked |
| [O28](#o28-real-absolute-value) | `abs(x)` | Real absolute value | checked |
| [O29](#o29-minimum-of-two-reals) | `min(a, b)` | Minimum of two reals | checked |
| [O30](#o30-maximum-of-two-reals) | `max(a, b)` | Maximum of two reals | checked |
| [O31](#o31-floor) | `floor(x)` | Floor | checked |
| [O32](#o32-ceiling) | `ceil(x)` | Ceiling | checked |
| [O33](#o33-sign) | `sign(x)` | Sign | checked |
| [O34](#o34-integer-remainder) | `a % d` | Integer remainder | checked |
| [O35](#o35-integer-quotient) | `quot(a, d)` | Integer quotient | checked |
| [O36](#o36-greatest-common-divisor) | `gcd(a, b)` | Greatest common divisor | checked |
| [O37](#o37-least-common-multiple) | `lcm(a, b)` | Least common multiple | checked |
| [O38](#o38-factorial) | `factorial(n); n!` | Factorial | checked |
| [O39](#o39-sine) | `sin(x)` | Sine | checked |
| [O40](#o40-cosine) | `cos(x)` | Cosine | checked |
| [O41](#o41-tangent) | `tan(x)` | Tangent | checked |
| [O42](#o42-cotangent) | `cot(x)` | Cotangent | checked |
| [O43](#o43-principal-arcsine) | `arcsin(x)` | Principal arcsine | checked |
| [O44](#o44-principal-arccosine) | `arccos(x)` | Principal arccosine | checked |
| [O45](#o45-principal-arctangent) | `arctan(x)` | Principal arctangent | checked |
| [O46](#o46-principal-arccotangent) | `arccot(x)` | Principal arccotangent | checked |
| [O47](#o47-exponential) | `exp(x)` | Exponential | checked |
| [O48](#o48-natural-logarithm) | `ln(x)` | Natural logarithm | checked |
| [O49](#o49-logarithm-with-specified-base) | `log(b, x)` | Logarithm with specified base | checked |
| [O50](#o50-principal-square-root) | `sqrt(x)` | Principal square root | checked |
| [O51](#o51-real-coordinate) | `re(z)` | Real coordinate | checked |
| [O52](#o52-imaginary-coordinate) | `img(z)` | Imaginary coordinate | checked |
| [O53](#o53-complex-modulus) | `C_abs(z)` | Complex modulus | checked |
| [O54](#o54-binary-union) | `union(A, B); A ∪ B` | Binary union | checked |
| [O55](#o55-binary-intersection) | `intersect(A, B); A ∩ B` | Binary intersection | checked |
| [O56](#o56-set-difference) | `set_minus(A, B)` | Set difference | checked |
| [O57](#o57-union-of-a-family) | `family_union(F)` | Union of a family | checked |
| [O58](#o58-intersection-of-a-family) | `family_intersect(F)` | Intersection of a family | checked |
| [O59](#o59-power-set) | `power_set(A)` | Power set | checked |
| [O60](#o60-indexed-union) | `index_union(I, X, A)` | Indexed union | checked |
| [O61](#o61-indexed-intersection) | `index_intersect(I, X, A)` | Indexed intersection | checked |
| [O62](#o62-indexed-cartesian-product) | `index_cart(I, S, g)` | Indexed Cartesian product | checked |
| [O63](#o63-finite-displayed-sets) | `{a, b, ...}; {}` | Finite displayed sets | checked |
| [O64](#o64-bounded-set-builders) | `{x A: filters}` | Bounded set builders | checked |
| [O65](#o65-half-open-integer-ranges) | `range(a, b)` | Half-open integer ranges | checked |
| [O66](#o66-closed-integer-ranges) | `closed_range(a, b); a...b` | Closed integer ranges | checked |
| [O67](#o67-finite-sequence-spaces) | `finite_seq(S, n)` | Finite sequence spaces | checked |
| [O68](#o68-infinite-sequence-spaces) | `seq(S)` | Infinite sequence spaces | checked |
| [O69](#o69-open-lower-rays) | `'(a,)` | Open lower rays | checked |
| [O70](#o70-closed-lower-rays) | `'[a,)` | Closed lower rays | checked |
| [O71](#o71-open-upper-rays) | `'(,b)` | Open upper rays | checked |
| [O72](#o72-closed-upper-rays) | `'(,b]` | Closed upper rays | checked |
| [O73](#o73-open-real-intervals) | `'(a,b)` | Open real intervals | checked |
| [O74](#o74-open-closed-real-intervals) | `'(a,b]` | Open-closed real intervals | checked |
| [O75](#o75-closed-open-real-intervals) | `'[a,b)` | Closed-open real intervals | checked |
| [O76](#o76-closed-real-intervals) | `'[a,b]` | Closed real intervals | checked |
| [O77](#o77-finite-cartesian-products) | `cart(S1, ..., Sn); S1 × S2` | Finite Cartesian products | checked |
| [O78](#o78-finite-tuples) | `(a, b, ...); tuple(a, ...); ()` | Finite tuples | checked |
| [O79](#o79-function-spaces) | `fn(parameters: guards) T` | Function spaces | checked |
| [O80](#o80-anonymous-functions) | `fn(parameters: guards) T {body}` | Anonymous functions | checked |
| [O81](#o81-function-images) | `fn_range(f)` | Function images | checked |
| [O82](#o82-sums-over-integer-ranges) | `sum(a,b,f)` | Sums over integer ranges | checked |
| [O83](#o83-products-over-integer-ranges) | `product(a,b,f)` | Products over integer ranges | checked |
| [O84](#o84-finite-set-sums) | `finite_set_sum(S,f)` | Finite-set sums | checked |
| [O85](#o85-finite-set-products) | `finite_set_product(S,f)` | Finite-set products | checked |
| [O86](#o86-ordered-folds) | `reduce(a,b,f,op,seed)` | Ordered folds | checked |
| [O87](#o87-finite-set-folds) | `finite_set_reduce(S,f,op,seed)` | Finite-set folds | checked |
| [O88](#o88-finite-cardinality) | `finite_set_size(S)` | Finite cardinality | checked |
| [O89](#o89-maximum-of-a-finite-set) | `finite_set_max(S)` | Maximum of a finite set | checked |
| [O90](#o90-minimum-of-a-finite-set) | `finite_set_min(S)` | Minimum of a finite set | checked |
| [O91](#o91-struct-carriers) | `&Name<arguments>` | Struct carriers | checked |
| [O92](#o92-definition-owned-field-access) | `value.field` | Definition-owned field access | checked |
| [O93](#o93-template-instances) | `\Name<arguments>` | Template instances | checked |

### O01. Division

**Public form:** `a / b`.

**Mathematical function:** divide a complex scalar by a nonzero complex scalar.
Real and rational inputs can support more specific result membership. Integer
inputs do not imply an integer quotient.

### Domain and well-definedness

| Obligation | Meaning | Typical way to establish it |
|---|---|---|
| Both child expressions are WD | Their names, applications, and internal operations are legal | Introduce their names; meet their own domain conditions |
| `b != 0` | The divisor is nonzero | A justified premise, a nonzero carrier, a positive carrier, or a proved inequality |
| `a $in C` | The dividend is a complex scalar | Stored carrier membership, numeric inclusion, or structural membership |
| `b $in C` | The divisor is a complex scalar | The same carrier routes |

The current WD implementation checks child objects first, then nonzero,
then the two complex memberships. A stated real carrier supports complex
membership through the numeric inclusion relationship; it does not supply
nonzeroness on its own.

For a theorem about arbitrary nonzero reals, the local premise is sufficient:

```litex
forall x R:
    x != 0
    =>:
        1 / x = 1 / x
```

The premise is part of the mathematical statement. It is not an assumption
that may be added to an unrelated theorem merely to make its proof pass.
For a reusable function, place the condition in the signature as in S01.

#### Common builtin properties

Every row below requires all expressions to be WD. Nonzero conditions needed
for division remain required even in a formula that looks trivially true.

| Property | Additional mathematical conditions | Current use |
|---|---|---|
| `a / 1 = a` | `a $in C` | State the equality directly |
| `0 / b = 0` | `b $in C`, `b != 0` | State the equality directly |
| `b / b = 1` | `b $in C`, `b != 0` | State the equality directly |
| `(a / b) * b = a` | `a, b $in C`, `b != 0` | Direct identity; useful as an algebraic bridge |
| `a / b $in R` | `a, b $in R`, `b != 0` | Carrier/structural membership after WD |
| `a / b != 0` | `a, b $in R`, `a != 0`, `b != 0` | Direct builtin verification in the checked example |

The first four identities are checked together here:

```litex
forall a, b C:
    b != 0
    =>:
        a / 1 = a
        0 / b = 0
        b / b = 1
        (a / b) * b = a
```

Closure in the reals:

```litex
forall a, b R:
    b != 0
    =>:
        a / b $in R
```

A nonzero numerator and divisor give a nonzero quotient:

```litex
forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0
```

These are representative native division properties. Rational carriers,
quotient/remainder, sign and other transformations are indexed through the
related object and atomic-fact entries; a larger combined expression may need
the explicit bridge described below.

#### Boundary: integer division

**Expected rejection — phase `search_proof`:**

<!-- litex:skip-test -->
```litex
have a Z = 1
have b Z = 2
a / b $in Z
```

`a / b` is meaningful here, but its value is `1 / 2`, which is not an integer.
The correction is to use the actual result carrier, or to supply and prove a
relevant divisibility condition when an integer result is mathematically needed.
Membership and nonmembership of this closed quotient are checked in F01.

**Evidence:** D01–D06.
**Source:** [division WD](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs),
[structural membership](../src/execute/execute_fact_stmt/verify_atomic_fact/search_structural_membership.rs),
[nonzero quotient rule](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_rules/not_equal.rs).
**Related:** [S01](#s01-expression-defined-functions), [P01](#p01-reflexivity-does-not-bypass-well-definedness),
[P04](#p04-connect-division-and-multiplication-explicitly).

### O02. Names and qualified references

**Public form:** `name; export::name; module::export::name; module:::name`.

**Mathematical function.** Refer to an introduced mathematical object or a visible exported definition. Qualified spelling changes lookup, not the object’s mathematical role.

**Well-definedness and domain.** The name and definition owner must be visible at this source position. Export loading order and manifest aliases govern qualified paths.

**Common native properties and proof routes.** Stored equality and carrier information can be reused. Equal aliases may support congruence; a name does not imply any arbitrary numerical value.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Undefined names and not-yet-loaded exports are rejected. Manifest dependencies are not source import statements. A two-step alias can require a direct value equality before arithmetic; the example deliberately exposes b = a = 2.

**Checked example.**

```litex
have a R = 2
a = 2
let b = a
b = a = 2
b + 1 = 3
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O02` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O03. Function applications

**Public form:** `f(arguments)`.

**Mathematical function.** Evaluate or refer to the value of a callable mathematical object at admissible arguments.

**Well-definedness and domain.** The callable signature is known; arity, every argument carrier, instantiated guards and nested call WD must verify. Finite function calls require their exact input domain.

**Common native properties and proof routes.** Legal applications satisfy the declared return carrier. Expression-defined functions expose defining equalities; opaque functions give no arbitrary evaluation formula.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A real input does not meet a nonzero guard by itself. Field, template and returned-function calls retain their own signature owner.

**Checked example.**

```litex
have fn shift(x R) R = x + 1
shift(2) = 3
forall x R:
    shift(x) $in R
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/core.rs); `O03` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S01 Expression-defined functions](#s01-expression-defined-functions), [S46 Function extensionality](#s46-function-extensionality).

### O04. Exact numeric literals

**Public form:** `integer or decimal literal`.

**Mathematical function.** Represent exact numeric constants; a decimal is an exact value rather than an approximate host float.

**Well-definedness and domain.** The token is a valid supported numeral. Negative literals use the unary negation operation.

**Common native properties and proof routes.** Closed arithmetic and numeric carrier membership use exact calculation. Natural numbers include zero.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A decimal’s appearance does not make it an integer. Use an explicit nonmembership check when needed.

**Checked example.**

```litex
0.1 + 0.2 = 0.3
1 / 2 $in Q
not 1 / 2 $in Z
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O04` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O05. Imaginary unit

**Public form:** `i`.

**Mathematical function.** The complex scalar whose square is -1.

**Well-definedness and domain.** Native named constant; no input-domain parameter.

**Common native properties and proof routes.** i $in C; re(i) = 0 and img(i) = 1; i^2 = -1.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A constant is an object; an equation or membership about it is a fact. Exact symbolic support does not imply arbitrary transcendental evaluation.

**Checked example.**

```litex
i^2 = -1
re(i) = 0
img(i) = 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O05` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O06. Euler’s number

**Public form:** `e`.

**Mathematical function.** The native positive real constant used by exponential and logarithm operations.

**Well-definedness and domain.** Native named constant; no input-domain parameter.

**Common native properties and proof routes.** e $in R+; exp(1) = e and ln(e) = 1.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A constant is an object; an equation or membership about it is a fact. Exact symbolic support does not imply arbitrary transcendental evaluation.

**Checked example.**

```litex
e $in R+
exp(1) = e
ln(e) = 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O06` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O07. Pi

**Public form:** `pi`.

**Mathematical function.** The native positive real circle constant used by trigonometric rules.

**Well-definedness and domain.** Native named constant; no input-domain parameter.

**Common native properties and proof routes.** pi $in R+; sin(pi) = 0 and cos(pi) = -1.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A constant is an object; an equation or membership about it is a fact. Exact symbolic support does not imply arbitrary transcendental evaluation.

**Checked example.**

```litex
pi $in R+
sin(pi) = 0
cos(pi) = -1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O07` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O08. Natural numbers including zero: N

**Public form:** `N`.

**Mathematical function.** Natural numbers including zero. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** 0 <= x. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
0 $in N
2 $in N
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O08` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O09. Positive natural numbers: N+

**Public form:** `N+; Z+`.

**Mathematical function.** Positive natural numbers. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** 0 < x; 0 <= x; x != 0. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
1 $in N+
2 $in Z+
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O09` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O10. Integers: Z

**Public form:** `Z`.

**Mathematical function.** Integers. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** Z is included in Q, R and C; integers are closed under +, -, *. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
-2 $in Z
0 $in Z
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O10` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O11. Rational numbers: Q

**Public form:** `Q`.

**Mathematical function.** Rational numbers. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** Q is included in R and C; division needs a nonzero divisor. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
1 / 2 $in Q
-3 $in Q
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O11` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O12. Real numbers: R

**Public form:** `R`.

**Mathematical function.** Real numbers. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** R is included in C; real arithmetic and order retain their domain guards. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
sqrt(2) $in R
1 / 2 $in R
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O12` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O13. Complex numbers: C

**Public form:** `C`.

**Mathematical function.** Complex numbers. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** Complex arithmetic is available; ordered comparisons still require real operands. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
i $in C
2 + 3 * i $in C
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O13` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O14. Positive rationals: Q+

**Public form:** `Q+`.

**Mathematical function.** Positive rationals. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** 0 < x; 0 <= x; x != 0; x $in Q. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
1 / 2 $in Q+
2 $in Q+
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O14` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O15. Positive reals: R+

**Public form:** `R+`.

**Mathematical function.** Positive reals. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** 0 < x; 0 <= x; x != 0; x $in R. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
1 / 2 $in R+
2 $in R+
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O15` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O16. Negative rationals: Q-

**Public form:** `Q-`.

**Mathematical function.** Negative rationals. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** x < 0; x <= 0; x != 0; x $in Q. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
-1 / 2 $in Q-
-2 $in Q-
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O16` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O17. Negative integers: Z-

**Public form:** `Z-`.

**Mathematical function.** Negative integers. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** x < 0; x <= 0; x != 0; x $in Z. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
-1 $in Z-
-2 $in Z-
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O17` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O18. Negative reals: R-

**Public form:** `R-`.

**Mathematical function.** Negative reals. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** x < 0; x <= 0; x != 0; x $in R. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
-1 / 2 $in R-
-2 $in R-
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O18` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O19. Nonzero rationals: Q*

**Public form:** `Q*`.

**Mathematical function.** Nonzero rationals. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** x != 0; x $in Q, without choosing its sign. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
1 / 2 $in Q*
-2 $in Q*
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O19` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O20. Nonzero integers: Z*

**Public form:** `Z*`.

**Mathematical function.** Nonzero integers. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** x != 0; x $in Z, without choosing its sign. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
1 $in Z*
-2 $in Z*
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O20` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O21. Nonzero reals: R*

**Public form:** `R*`.

**Mathematical function.** Nonzero reals. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** x != 0; x $in R, without choosing its sign. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
1 / 2 $in R*
-2 $in R*
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O21` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O22. Nonzero complexes: C*

**Public form:** `C*`.

**Mathematical function.** Nonzero complexes. These are mathematical set objects, not different runtime host types.

**Well-definedness and domain.** Native set object. Membership and a typed declaration establish facts about its elements; the set object itself requires no input guard.

**Common native properties and proof routes.** x != 0; x $in C; real sign is not available for general complex values. Signed/nonzero consequences are stored by inference; widening to larger standard carriers is available to structural membership checking.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Base-carrier membership does not imply a sign, nonzeroness, or a concrete value. Z+ is the supported alias for N+; do not infer undocumented underscore aliases.

**Checked example.**

```litex
i $in C*
2 $in C*
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O22` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O23. Addition

**Public form:** `a + b`.

**Mathematical function.** Scalar addition.

**Well-definedness and domain.** a, b $in C. Every child expression must first be WD.

**Common native properties and proof routes.** Commutativity, associativity, zero identity, and appropriate numeric carrier closure.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Integers/reals widen to C; a general complex result is not automatically ordered.

**Checked example.**

```litex
2 + 3 = 5
forall a, b C:
    a + b = b + a
    a + 0 = a
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O23` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O24. Subtraction

**Public form:** `a - b`.

**Mathematical function.** Scalar difference.

**Well-definedness and domain.** a, b $in C. Every child expression must first be WD.

**Common native properties and proof routes.** a - a = 0; a - 0 = a; integer/real/complex closure.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Natural-number subtraction can be negative; N is not closed under arbitrary subtraction.

**Checked example.**

```litex
3 - 5 = -2
forall a C:
    a - a = 0
    a - 0 = a
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O24` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O25. Additive inverse

**Public form:** `-a`.

**Mathematical function.** The additive inverse of a scalar.

**Well-definedness and domain.** a $in C. Every child expression must first be WD.

**Common native properties and proof routes.** -(-a) = a; a + (-a) = 0; appropriate carrier closure.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Unary minus is distinct from binary subtraction and does not supply order on general C.

**Checked example.**

```litex
-(-3) = 3
forall a C:
    a + (-a) = 0
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O25` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O26. Multiplication

**Public form:** `a * b`.

**Mathematical function.** Scalar multiplication.

**Well-definedness and domain.** a, b $in C. Every child expression must first be WD.

**Common native properties and proof routes.** Commutativity, associativity, one/zero identities and carrier closure.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Cancelling a factor requires a justified nonzero condition; zero factors cannot be divided away.

**Checked example.**

```litex
2 * 3 = 6
forall a, b C:
    a * b = b * a
    a * 1 = a
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O26` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O27. Powers

**Public form:** `a^b`.

**Mathematical function.** A native scalar power in a supported domain branch.

**Well-definedness and domain.** R or C base with exponent in N; nonzero C base with exponent in Z; also closed positive rational base with a rational noninteger exponent. Every child expression must first be WD.

**Common native properties and proof routes.** Closed powers and supported exponent identities. Natural exponent zero uses the native a^0 = 1 convention.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A symbolic positive real base with an arbitrary real exponent is not licensed by the current branch list. Negative integer exponents require nonzero base.

**Checked example.**

```litex
2^3 = 8
4^(1 / 2) = 2
2^(-1) = 1 / 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O27` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O28. Real absolute value

**Public form:** `abs(x)`.

**Mathematical function.** The nonnegative magnitude of a real scalar.

**Well-definedness and domain.** x $in R. Every child expression must first be WD.

**Common native properties and proof routes.** abs(-x) = abs(x); abs(x) >= 0; square/magnitude and signed-value rules.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Use C_abs for a general complex value rather than silently treating i as real.

**Checked example.**

```litex
abs(-3) = 3
abs(0) = 0
forall x R:
    abs(x) >= 0
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O28` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O29. Minimum of two reals

**Public form:** `min(a, b)`.

**Mathematical function.** The smaller of two real numbers.

**Well-definedness and domain.** a, b $in R. Every child expression must first be WD.

**Common native properties and proof routes.** Commutativity, idempotence and lower-bound laws.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Arguments are real, not arbitrary sets or unordered complex scalars.

**Checked example.**

```litex
min(3, 2) = 2
forall x R:
    min(x, x) = x
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O29` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O30. Maximum of two reals

**Public form:** `max(a, b)`.

**Mathematical function.** The larger of two real numbers.

**Well-definedness and domain.** a, b $in R. Every child expression must first be WD.

**Common native properties and proof routes.** Commutativity, idempotence and upper-bound laws.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The binary operator differs from finite_set_max, whose input is one finite nonempty set.

**Checked example.**

```litex
max(-1, 2) = 2
forall x R:
    max(x, x) = x
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O30` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O31. Floor

**Public form:** `floor(x)`.

**Mathematical function.** The greatest integer no greater than x.

**Well-definedness and domain.** x $in R. Every child expression must first be WD.

**Common native properties and proof routes.** Integer result; floor(x) <= x < floor(x) + 1; exact values for closed inputs.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** For a negative input, floor rounds toward negative infinity, not toward zero.

**Checked example.**

```litex
floor(3.7) = 3
floor(-1.2) = -2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O31` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O32. Ceiling

**Public form:** `ceil(x)`.

**Mathematical function.** The least integer no less than x.

**Well-definedness and domain.** x $in R. Every child expression must first be WD.

**Common native properties and proof routes.** Integer result; ceil(x) - 1 < x <= ceil(x); exact values for closed inputs.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Ceiling and floor differ at noninteger arguments, including negative ones.

**Checked example.**

```litex
ceil(3.2) = 4
ceil(-1.2) = -1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O32` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O33. Sign

**Public form:** `sign(x)`.

**Mathematical function.** The real sign value -1, 0 or 1.

**Well-definedness and domain.** x $in R. Every child expression must first be WD.

**Common native properties and proof routes.** Integer codomain and branches determined by positive, zero or negative x.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** This is real sign, not the phase of a complex number.

**Checked example.**

```litex
sign(-3) = -1
sign(0) = 0
sign(2) = 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O33` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O34. Integer remainder

**Public form:** `a % d`.

**Mathematical function.** Native integer remainder.

**Well-definedness and domain.** a, d $in Z and d != 0. Child WD is also required.

**Common native properties and proof routes.** For a positive divisor, the remainder is in [0,d). Closed signed dividends use the Euclidean remainder convention.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The divisor cannot be zero; this differs from real division.

**Checked example.**

```litex
(-7) % 3 = 2
7 % 3 = 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O34` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O35. Integer quotient

**Public form:** `quot(a, d)`.

**Mathematical function.** The integer quotient in a = d * quot(a,d) + a % d.

**Well-definedness and domain.** a $in Z; d $in N+. Child WD is also required.

**Common native properties and proof routes.** Integer result and the quotient/remainder decomposition for a positive divisor.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The quotient interface requires a positive divisor, stricter than modulo’s nonzero integer divisor.

**Checked example.**

```litex
quot(-7, 3) = -3
quot(7, 3) = 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O35` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O36. Greatest common divisor

**Public form:** `gcd(a, b)`.

**Mathematical function.** The positive greatest common divisor of an integer pair not both zero.

**Well-definedness and domain.** a, b $in Z; a != 0 or b != 0. Child WD is also required.

**Common native properties and proof routes.** Positive natural result; sign-insensitivity, common divisibility and familiar closed values.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The disjunction excludes only the all-zero pair; proving one particular operand nonzero is not always necessary.

**Checked example.**

```litex
gcd(54, -24) = 6
gcd(0, 3) = 3
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O36` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O37. Least common multiple

**Public form:** `lcm(a, b)`.

**Mathematical function.** The nonnegative least common multiple of two integers.

**Well-definedness and domain.** a, b $in Z. Child WD is also required.

**Common native properties and proof routes.** Natural result; zero-input and sign-insensitivity laws.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Unlike gcd, lcm permits the all-zero pair. Distinguish the two domain contracts.

**Checked example.**

```litex
lcm(12, -18) = 36
lcm(0, 3) = 0
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O37` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O38. Factorial

**Public form:** `factorial(n); n!`.

**Mathematical function.** The factorial of a natural number.

**Well-definedness and domain.** n $in N. Child WD is also required.

**Common native properties and proof routes.** Positive natural result; 0! = 1 and the successor recurrence.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Negative or noninteger arguments do not satisfy the native factorial domain.

**Checked example.**

```litex
0! = 1
3! = 6
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O38` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O39. Sine

**Public form:** `sin(x)`.

**Mathematical function.** Sine as a native real operation.

**Well-definedness and domain.** x $in R. Establish guards before using the object.

**Common native properties and proof routes.** Real result, bounded by -1 and 1; oddness, periodicity and the Pythagorean identity.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Inverse composition in the opposite direction needs a principal-range restriction. Realness alone does not supply tangent/cotangent nonzero denominators.

**Checked example.**

```litex
sin(0) = 0
sin(pi / 2) = 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O39` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O40. Cosine

**Public form:** `cos(x)`.

**Mathematical function.** Cosine as a native real operation.

**Well-definedness and domain.** x $in R. Establish guards before using the object.

**Common native properties and proof routes.** Real result, bounded by -1 and 1; evenness, periodicity and the Pythagorean identity.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Inverse composition in the opposite direction needs a principal-range restriction. Realness alone does not supply tangent/cotangent nonzero denominators.

**Checked example.**

```litex
cos(0) = 1
cos(pi) = -1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O40` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O41. Tangent

**Public form:** `tan(x)`.

**Mathematical function.** Tangent as a native real operation.

**Well-definedness and domain.** x $in R; cos(x) != 0. Establish guards before using the object.

**Common native properties and proof routes.** Real result; tan(x) = sin(x) / cos(x) in its domain.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Inverse composition in the opposite direction needs a principal-range restriction. Realness alone does not supply tangent/cotangent nonzero denominators.

**Checked example.**

```litex
tan(0) = 0
tan(pi / 4) = 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O41` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O42. Cotangent

**Public form:** `cot(x)`.

**Mathematical function.** Cotangent as a native real operation.

**Well-definedness and domain.** x $in R; sin(x) != 0. Establish guards before using the object.

**Common native properties and proof routes.** Real result; cot(x) = cos(x) / sin(x) in its domain.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Inverse composition in the opposite direction needs a principal-range restriction. Realness alone does not supply tangent/cotangent nonzero denominators.

**Checked example.**

```litex
cot(pi / 4) = 1
cot(pi / 2) = 0
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O42` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O43. Principal arcsine

**Public form:** `arcsin(x)`.

**Mathematical function.** Principal arcsine as a native real operation.

**Well-definedness and domain.** x $in R; -1 <= x <= 1. Establish guards before using the object.

**Common native properties and proof routes.** Principal real result; sin(arcsin(x)) = x on [-1,1].

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Inverse composition in the opposite direction needs a principal-range restriction. Realness alone does not supply tangent/cotangent nonzero denominators.

**Checked example.**

```litex
arcsin(0) = 0
arcsin(1) = pi / 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O43` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O44. Principal arccosine

**Public form:** `arccos(x)`.

**Mathematical function.** Principal arccosine as a native real operation.

**Well-definedness and domain.** x $in R; -1 <= x <= 1. Establish guards before using the object.

**Common native properties and proof routes.** Principal real result; cos(arccos(x)) = x on [-1,1].

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Inverse composition in the opposite direction needs a principal-range restriction. Realness alone does not supply tangent/cotangent nonzero denominators.

**Checked example.**

```litex
arccos(1) = 0
arccos(0) = pi / 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O44` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O45. Principal arctangent

**Public form:** `arctan(x)`.

**Mathematical function.** Principal arctangent as a native real operation.

**Well-definedness and domain.** x $in R. Establish guards before using the object.

**Common native properties and proof routes.** Principal real result; tan(arctan(x)) = x, with its principal-range domain facts.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Inverse composition in the opposite direction needs a principal-range restriction. Realness alone does not supply tangent/cotangent nonzero denominators. The initial bare arctan(1) = pi / 4 goal missed current search; this entry demonstrates valid real output without claiming that exact evaluation route.

**Checked example.**

```litex
arctan(0) = 0
arctan(1) $in R
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O45` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O46. Principal arccotangent

**Public form:** `arccot(x)`.

**Mathematical function.** Principal arccotangent as a native real operation.

**Well-definedness and domain.** x $in R. Establish guards before using the object.

**Common native properties and proof routes.** Principal real result; cot(arccot(x)) = x; the zero value is pi/2 in the native convention.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Inverse composition in the opposite direction needs a principal-range restriction. Realness alone does not supply tangent/cotangent nonzero denominators. The initial bare arccot(1) = pi / 4 goal missed current search; the exact zero value and real-output membership are checked separately.

**Checked example.**

```litex
arccot(0) = pi / 2
arccot(1) $in R
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O46` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O47. Exponential

**Public form:** `exp(x)`.

**Mathematical function.** The native real exponential.

**Well-definedness and domain.** x $in R. Child WD also applies.

**Common native properties and proof routes.** Positive real codomain; exp(0) = 1; exp(1) = e; exponential/logarithm identities.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** exp(x) has its own primitive domain; spelling e^x does not automatically license every symbolic real power.

**Checked example.**

```litex
exp(0) = 1
exp(1) = e
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O47` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O48. Natural logarithm

**Public form:** `ln(x)`.

**Mathematical function.** The natural logarithm of a positive real.

**Well-definedness and domain.** x $in R; x > 0. Child WD also applies.

**Common native properties and proof routes.** Real codomain; ln(1) = 0; ln(e) = 1; inverse relations with exp.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Nonzero alone permits negative reals and is insufficient for ln.

**Checked example.**

```litex
ln(1) = 0
ln(e) = 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O48` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O49. Logarithm with specified base

**Public form:** `log(b, x)`.

**Mathematical function.** The real logarithm of x with base b.

**Well-definedness and domain.** b, x $in R; b > 0; b != 1; x > 0. Child WD also applies.

**Common native properties and proof routes.** log(b,1) = 0; log(b,b) = 1 under the exact base/argument conditions.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Argument order is base then value. A positive base equal to one remains invalid.

**Checked example.**

```litex
log(2, 8) = 3
log(2, 1) = 0
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O49` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O50. Principal square root

**Public form:** `sqrt(x)`.

**Mathematical function.** The nonnegative real square root.

**Well-definedness and domain.** x $in R; 0 <= x. Child WD also applies.

**Common native properties and proof routes.** Nonnegative real codomain; sqrt(x)^2 = x and sqrt(x^2) = abs(x) for real x.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A complex square-root interpretation is not supplied by this real primitive; sqrt(x^2) is not x for arbitrary real x.

**Checked example.**

```litex
sqrt(4) = 2
sqrt((-3)^2) = abs(-3) = 3
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O50` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O51. Real coordinate

**Public form:** `re(z)`.

**Mathematical function.** The real coordinate of a complex scalar.

**Well-definedness and domain.** z $in C.

**Common native properties and proof routes.** Real result and the scalar reconstruction z = re(z) + img(z) * i.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** img(z) is a real coefficient, not img(z) * i. Use abs only for a real argument.

**Checked example.**

```litex
re(2 + 3 * i) = 2
re(i) = 0
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O51` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O52. Imaginary coordinate

**Public form:** `img(z)`.

**Mathematical function.** The real coefficient of i in a complex scalar.

**Well-definedness and domain.** z $in C.

**Common native properties and proof routes.** Real result; img(i) = 1 and img(real) = 0.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** img(z) is a real coefficient, not img(z) * i. Use abs only for a real argument.

**Checked example.**

```litex
img(2 + 3 * i) = 3
img(2) = 0
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O52` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O53. Complex modulus

**Public form:** `C_abs(z)`.

**Mathematical function.** The nonnegative real modulus of a complex scalar.

**Well-definedness and domain.** z $in C.

**Common native properties and proof routes.** Nonnegative real result; squared modulus is re(z)^2 + img(z)^2; agrees with abs for real z.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** img(z) is a real coefficient, not img(z) * i. Use abs only for a real argument.

**Checked example.**

```litex
C_abs(i) = 1
C_abs(-3) = 3
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs); `O53` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [O01 Division](#o01-division).

### O54. Binary union

**Public form:** `union(A, B); A ∪ B`.

**Mathematical function.** The union of two sets.

**Well-definedness and domain.** Child set objects must be WD. In Litex’s pure-set foundation, these constructors do not introduce a new universal host carrier.

**Common native properties and proof routes.** Membership gives a disjunction; commutativity, associativity, idempotence and empty-set identity.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Membership introduction and elimination can have different proof routes. A conjunction does not select a disjunct or an existential witness automatically.

**Checked example.**

```litex
union(R, Z) = union(Z, R)
union({1}, {}) = {1}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O54` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O55. Binary intersection

**Public form:** `intersect(A, B); A ∩ B`.

**Mathematical function.** The intersection of two sets.

**Well-definedness and domain.** Child set objects must be WD. In Litex’s pure-set foundation, these constructors do not introduce a new universal host carrier.

**Common native properties and proof routes.** Membership exposes both memberships; commutativity, associativity, idempotence and empty-set laws.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Membership introduction and elimination can have different proof routes. A conjunction does not select a disjunct or an existential witness automatically.

**Checked example.**

```litex
intersect(R, Z) = intersect(Z, R)
intersect({1}, {}) = {}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O55` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O56. Set difference

**Public form:** `set_minus(A, B)`.

**Mathematical function.** Elements of A not in B.

**Well-definedness and domain.** Child set objects must be WD. In Litex’s pure-set foundation, these constructors do not introduce a new universal host carrier.

**Common native properties and proof routes.** Membership exposes x in A and not x in B; difference by the empty set and by itself.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Membership introduction and elimination can have different proof routes. A conjunction does not select a disjunct or an existential witness automatically.

**Checked example.**

```litex
set_minus({1}, {1}) = {}
set_minus(R, {}) = R
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O56` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O57. Union of a family

**Public form:** `family_union(F)`.

**Mathematical function.** The union of all member sets in a family.

**Well-definedness and domain.** Child set objects must be WD. In Litex’s pure-set foundation, these constructors do not introduce a new universal host carrier.

**Common native properties and proof routes.** Membership has an intermediate member-set witness; singleton-family and power-set union identities.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Membership introduction and elimination can have different proof routes. A conjunction does not select a disjunct or an existential witness automatically.

**Checked example.**

```litex
family_union({{1, 2}}) = {1, 2}
family_union(power_set({1, 2})) = {1, 2}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O57` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O58. Intersection of a family

**Public form:** `family_intersect(F)`.

**Mathematical function.** The native family intersection.

**Well-definedness and domain.** Child set objects must be WD. In Litex’s pure-set foundation, these constructors do not introduce a new universal host carrier.

**Common native properties and proof routes.** A member belongs to every member set; singleton-family identity; quantified membership introduction uses a reserved theorem.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Membership introduction and elimination can have different proof routes. A conjunction does not select a disjunct or an existential witness automatically. The membership release takes the family_intersect object as its second argument, not the raw family.

**Checked example.**

```litex
$is_set(family_intersect({{1}}))
1 $in {1}
forall A {{1}}:
    1 $in A
release thm family_intersect_member(1, family_intersect({{1}}))
1 $in family_intersect({{1}})
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O58` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S25 Publish theorem conclusions](#s25-publish-theorem-conclusions).

### O59. Power set

**Public form:** `power_set(A)`.

**Mathematical function.** The set of subsets of A.

**Well-definedness and domain.** Child set objects must be WD. In Litex’s pure-set foundation, these constructors do not introduce a new universal host carrier.

**Common native properties and proof routes.** B in power_set(A) corresponds to B subset A; {} and A are members; membership supplies a subset interface.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Membership introduction and elimination can have different proof routes. A conjunction does not select a disjunct or an existential witness automatically.

**Checked example.**

```litex
{} $in power_set({1, 2})
by def {1} $subset {1, 2}
{1} $in power_set({1, 2})
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O59` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O60. Indexed union

**Public form:** `index_union(I, X, A)`.

**Mathematical function.** Union of a nonempty indexed family of subsets of X.

**Well-definedness and domain.** I is nonempty; I and X are sets; A belongs to fn(k I) power_set(X). All three objects are WD.

**Common native properties and proof routes.** A singleton index identifies the family member. Intersection membership introduction requires pointwise membership and index_intersect_member; union membership exposes an index witness.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The current WD contract excludes an empty index even if a different mathematical convention could assign it a value. The family’s return carrier must be the required power set.

**Checked example.**

```litex
let family = fn(k {1}) power_set(N) {{1}}
let result = index_union({1}, N, family)
$is_set(result)
result = result
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O60` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S25 Publish theorem conclusions](#s25-publish-theorem-conclusions).

### O61. Indexed intersection

**Public form:** `index_intersect(I, X, A)`.

**Mathematical function.** Intersection in ambient X of a nonempty indexed family.

**Well-definedness and domain.** I is nonempty; I and X are sets; A belongs to fn(k I) power_set(X). All three objects are WD.

**Common native properties and proof routes.** A singleton index identifies the family member. Intersection membership introduction requires pointwise membership and index_intersect_member; union membership exposes an index witness.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The current WD contract excludes an empty index even if a different mathematical convention could assign it a value. The family’s return carrier must be the required power set.

**Checked example.**

```litex
let family = fn(k {1}) power_set(N) {{1}}
let result = index_intersect({1}, N, family)
$is_set(result)
result = result
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O61` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S25 Publish theorem conclusions](#s25-publish-theorem-conclusions).

### O62. Indexed Cartesian product

**Public form:** `index_cart(I, S, g)`.

**Mathematical function.** The set of choice-like functions selecting one value from each indexed member g(alpha).

**Well-definedness and domain.** I is a nonempty set; S is a nonempty family-set carrier; g belongs to fn(alpha I) S. The native membership contract retains the complete input domain.

**Common native properties and proof routes.** A candidate’s pointwise selections can be introduced through index_cart_member. Nonemptiness from nonempty factors uses the explicit Choice-based native interfaces; product WD alone does not prove that factors are nonempty.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Knowing g is a function does not establish every factor is nonempty. Do not infer construction projections or a Cartesian dimension.

**Checked example.**

```litex
let family = fn(k {1}) power_set(N) {{1}}
let product_set = index_cart({1}, power_set(N), family)
$is_set(product_set)
product_set = product_set
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O62` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S25 Publish theorem conclusions](#s25-publish-theorem-conclusions).

### O63. Finite displayed sets

**Public form:** `{a, b, ...}; {}`.

**Mathematical function.** Construct a finite set from an explicit list of distinct values.

**Well-definedness and domain.** Each element is WD; every pair of displayed elements must verify unequal. The empty list requires no element or distinctness proof.

**Common native properties and proof routes.** Finiteness and displayed cardinality; singleton membership implies equality, and longer-list membership exposes equality alternatives. Displayed membership can use a matching element equality.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Unlike informal set notation, duplicate entries or unknown pairwise inequality can fail WD. Distinctness is part of this constructor contract.

**Checked example.**

```litex
$is_finite_set({1, 2})
finite_set_size({1, 2}) = 2
1 $in {1, 2}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O63` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O64. Bounded set builders

**Public form:** `{x A: filters}`.

**Mathematical function.** Form the subset of a given base set consisting of values satisfying quantifier-free filters.

**Well-definedness and domain.** The base object is WD; bind x locally and check the filters in their source order. Valid earlier guards can license later partial expressions.

**Common native properties and proof routes.** Membership projects the base membership and instantiated filters. Introduction can explicitly verify those conditions through set_builder_member; alpha-equivalent bound names describe the same builder.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** This is bounded separation, not unrestricted comprehension over a universal set. A direct forall filter must be packaged in real concrete predicate vocabulary.

**Checked example.**

```litex
release thm set_builder_member(2, {x R: x > 0})
forall x {t R: t > 0}:
    x $in R
    x > 0
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/binder.rs); `O64` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O65. Half-open integer ranges

**Public form:** `range(a, b)`.

**Mathematical function.** Integers n with a <= n < b.

**Well-definedness and domain.** a, b $in Z; child WD. The range object does not require a <= b.

**Common native properties and proof routes.** Finite membership bounds and finite expansion; reversed or equal endpoints give an empty range.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Check which upper endpoint convention the proof or iteration statement expects.

**Checked example.**

```litex
1 $in range(1, 3)
not 3 $in range(1, 3)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs); `O65` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O66. Closed integer ranges

**Public form:** `closed_range(a, b); a...b`.

**Mathematical function.** Integers n with a <= n <= b.

**Well-definedness and domain.** a, b $in Z; child WD. The range object does not require a <= b.

**Common native properties and proof routes.** Finite membership bounds and expansion including the upper endpoint; reversed endpoints give an empty range.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Check which upper endpoint convention the proof or iteration statement expects.

**Checked example.**

```litex
2 $in closed_range(1, 2)
2 $in 1...2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs); `O66` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O67. Finite sequence spaces

**Public form:** `finite_seq(S, n)`.

**Mathematical function.** Functions on the exact finite index domain 1 through n, with values in S.

**Well-definedness and domain.** S is WD as a set and n belongs to N. A member’s calls require an index in its complete input domain.

**Common native properties and proof routes.** Equals fn(k closed_range(1,n)) S, with the zero-length domain {}. Coordinate membership is ordinary callable membership, not an attached tuple_dim.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A function merely defined at some coordinates need not have this complete domain. Index zero and n+1 are outside a positive length-n sequence.

**Checked example.**

```litex
finite_seq(R, 0) = fn(k {}) R
finite_seq(R, 2) = fn(k closed_range(1, 2)) R
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs); `O67` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S01 Expression-defined functions](#s01-expression-defined-functions), [S46 Function extensionality](#s46-function-extensionality).

### O68. Infinite sequence spaces

**Public form:** `seq(S)`.

**Mathematical function.** Functions from positive natural indices to S.

**Well-definedness and domain.** S is a WD set object. Sequence calls require positive natural indices.

**Common native properties and proof routes.** seq(S) equals fn(k N+) S. Legal calls inherit the return-carrier membership; function-space membership introduction has a native theorem interface.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The sequence convention is one-based; do not assume that index zero is admitted.

**Checked example.**

```litex
seq(R) = fn(k N+) R
seq(N) = fn(k N+) N
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs); `O68` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S01 Expression-defined functions](#s01-expression-defined-functions), [S46 Function extensionality](#s46-function-extensionality).

### O69. Open lower rays

**Public form:** `'(a,)`.

**Mathematical function.** Real values greater than a.

**Well-definedness and domain.** The finite endpoint is WD and belongs to R.

**Common native properties and proof routes.** Membership gives realness and the indicated strict or weak bound; the ray is a subset of R.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The apostrophe is the interval prefix. Missing infinite endpoints are notation, not an infinity object usable in arithmetic.

**Checked example.**

```litex
1 $in '(0,)
not 0 $in '(0,)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O69` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O70. Closed lower rays

**Public form:** `'[a,)`.

**Mathematical function.** Real values greater than or equal to a.

**Well-definedness and domain.** The finite endpoint is WD and belongs to R.

**Common native properties and proof routes.** Membership gives realness and the indicated strict or weak bound; the ray is a subset of R.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The apostrophe is the interval prefix. Missing infinite endpoints are notation, not an infinity object usable in arithmetic.

**Checked example.**

```litex
0 $in '[0,)
1 $in '[0,)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O70` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O71. Open upper rays

**Public form:** `'(,b)`.

**Mathematical function.** Real values less than b.

**Well-definedness and domain.** The finite endpoint is WD and belongs to R.

**Common native properties and proof routes.** Membership gives realness and the indicated strict or weak bound; the ray is a subset of R.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The apostrophe is the interval prefix. Missing infinite endpoints are notation, not an infinity object usable in arithmetic.

**Checked example.**

```litex
-1 $in '(,0)
not 0 $in '(,0)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O71` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O72. Closed upper rays

**Public form:** `'(,b]`.

**Mathematical function.** Real values less than or equal to b.

**Well-definedness and domain.** The finite endpoint is WD and belongs to R.

**Common native properties and proof routes.** Membership gives realness and the indicated strict or weak bound; the ray is a subset of R.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The apostrophe is the interval prefix. Missing infinite endpoints are notation, not an infinity object usable in arithmetic.

**Checked example.**

```litex
0 $in '(,0]
-1 $in '(,0]
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O72` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O73. Open real intervals

**Public form:** `'(a,b)`.

**Mathematical function.** The subset of reals satisfying a < x < b.

**Well-definedness and domain.** Both endpoints are WD and belong to R. Reversed endpoints still form a WD empty interval.

**Common native properties and proof routes.** Membership exposes the precise endpoint inequalities; changing a bracket changes boundary membership.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** These are real intervals. range and closed_range are integer sets and have different finiteness consequences.

**Checked example.**

```litex
1 $in '(0,2)
not 0 $in '(0,2)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O73` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O74. Open-closed real intervals

**Public form:** `'(a,b]`.

**Mathematical function.** The subset of reals satisfying a < x <= b.

**Well-definedness and domain.** Both endpoints are WD and belong to R. Reversed endpoints still form a WD empty interval.

**Common native properties and proof routes.** Membership exposes the precise endpoint inequalities; changing a bracket changes boundary membership.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** These are real intervals. range and closed_range are integer sets and have different finiteness consequences.

**Checked example.**

```litex
2 $in '(0,2]
not 0 $in '(0,2]
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O74` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O75. Closed-open real intervals

**Public form:** `'[a,b)`.

**Mathematical function.** The subset of reals satisfying a <= x < b.

**Well-definedness and domain.** Both endpoints are WD and belong to R. Reversed endpoints still form a WD empty interval.

**Common native properties and proof routes.** Membership exposes the precise endpoint inequalities; changing a bracket changes boundary membership.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** These are real intervals. range and closed_range are integer sets and have different finiteness consequences.

**Checked example.**

```litex
0 $in '[0,2)
not 2 $in '[0,2)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O75` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O76. Closed real intervals

**Public form:** `'[a,b]`.

**Mathematical function.** The subset of reals satisfying a <= x <= b.

**Well-definedness and domain.** Both endpoints are WD and belong to R. Reversed endpoints still form a WD empty interval.

**Common native properties and proof routes.** Membership exposes the precise endpoint inequalities; changing a bracket changes boundary membership.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** These are real intervals. range and closed_range are integer sets and have different finiteness consequences.

**Checked example.**

```litex
0 $in '[0,2]
2 $in '[0,2]
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O76` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O77. Finite Cartesian products

**Public form:** `cart(S1, ..., Sn); S1 × S2`.

**Mathematical function.** The set of exact finite functions whose k-th value lies in the k-th factor.

**Well-definedness and domain.** All factor objects are WD. Membership checks the candidate’s complete finite input domain and all coordinate conditions.

**Common native properties and proof routes.** Coordinate membership; zero factors give a singleton containing the empty function; finite cardinality is the product of factor cardinalities; an empty factor makes a nonzero-factor product empty.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A Cartesian set has no retained construction dimension or projection operator. Equal Cartesian sets are not distinguished by the expression used to construct them.

**Checked example.**

```litex
(1, 2) $in cart(R, Z)
() $in cart()
finite_set_size(cart()) = 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O77` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O78. Finite tuples

**Public form:** `(a, b, ...); tuple(a, ...); ()`.

**Mathematical function.** An exact finite function on indices 1 through its displayed length, with the displayed values.

**Well-definedness and domain.** Each component is WD. Calls to a named tuple require an in-domain index and its checked finite-function interface.

**Common native properties and proof routes.** Coordinate values and exact finite-sequence membership. Equality from coordinates requires both complete domains and every coordinate, through tuple_equal_from_coordinates.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Use ordinary function calls on a named value; old [index] syntax and tuple_dim are removed. A singleton uses tuple(value), since (value) is grouping.

**Checked example.**

```litex
have p cart(R, Z) = (1, 2)
p(1) = 1
p(2) = 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O78` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O79. Function spaces

**Public form:** `fn(parameters: guards) T`.

**Mathematical function.** A set of functions having the complete input domain described by the parameter carriers and guards, returning values in T.

**Well-definedness and domain.** Parameter carrier objects, guards and return set are WD. Current signature carriers cannot refer to this signature’s own parameter names; enclosing parameters may be used.

**Common native properties and proof routes.** Membership supplies callable domain and return contracts. Alpha-renamed parameters give an equivalent signature; explicit fn_set_member checks the full pointwise obligation.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A function-space object is not itself a function to call. A return bound is not automatically the actual image.

**Checked example.**

```litex
have fn identity(x R) R = x
identity $in fn(t R) R
fn(x R) R = fn(t R) R
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/binder.rs); `O79` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S01 Expression-defined functions](#s01-expression-defined-functions), [S46 Function extensionality](#s46-function-extensionality).

### O80. Anonymous functions

**Public form:** `fn(parameters: guards) T {body}`.

**Mathematical function.** Construct a function directly from an expression without introducing a name.

**Well-definedness and domain.** The function-space checks apply; under its local binders/guards the body is WD and belongs to T. The empty-complete-domain exception only concerns pointwise return membership, not body WD.

**Common native properties and proof routes.** A matching function-space membership and checked beta/evaluation equalities. Named or direct applications use the same domain conditions.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Writing the desired T cannot make an incompatible body return-typed. Use a real guard for a partial expression.

**Checked example.**

```litex
fn(x R) R {x + 1}(2) = 3
fn(x R: x != 0) R {1 / x}(2) = 1 / 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/binder.rs); `O80` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S01 Expression-defined functions](#s01-expression-defined-functions), [S46 Function extensionality](#s46-function-extensionality).

### O81. Function images

**Public form:** `fn_range(f)`.

**Mathematical function.** The actual image of a function, rather than its declared return bound.

**Well-definedness and domain.** f is WD and has a known callable function-space interface.

**Common native properties and proof routes.** A legal application lies in its image; image membership supports preimage extraction. A constant function on a proved nonempty domain has a singleton image.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The image need not equal the codomain. Empty input domains give an empty image, even for a written constant body.

**Checked example.**

```litex
have fn constant(x R) R = 1
fn_range(constant) = {1}
constant(2) $in fn_range(constant)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/core.rs); `O81` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S01 Expression-defined functions](#s01-expression-defined-functions), [S46 Function extensionality](#s46-function-extensionality).

### O82. Sums over integer ranges

**Public form:** `sum(a,b,f)`.

**Mathematical function.** The inclusive scalar sum over integer indices a through b.

**Well-definedness and domain.** a,b in Z; a <= b; f unary, defined throughout the index range, with return carrier a subset of C. All child objects are WD.

**Common native properties and proof routes.** Scalar carrier closure, singleton and splitting identities, and pointwise comparison through explicit native theorem interfaces.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Unlike range(a,b), this operator includes b; its current WD contract does not admit a reversed empty range.

**Checked example.**

```litex
sum(1, 3, fn(k Z) Z {k}) = 6
sum(2, 2, fn(k Z) Z {k}) = 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs); `O82` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O83. Products over integer ranges

**Public form:** `product(a,b,f)`.

**Mathematical function.** The inclusive scalar product over integer indices a through b.

**Well-definedness and domain.** The same index/domain/scalar-return requirements as sum. All child objects are WD.

**Common native properties and proof routes.** Scalar carrier closure, singleton and splitting identities, and nonzero-factor properties.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A usable callable signature must cover every index, not merely the two endpoints.

**Checked example.**

```litex
product(1, 3, fn(k Z) Z {k}) = 6
product(2, 2, fn(k Z) Z {k}) = 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs); `O83` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O84. Finite-set sums

**Public form:** `finite_set_sum(S,f)`.

**Mathematical function.** A scalar sum indexed by a finite set.

**Well-definedness and domain.** S finite; f unary with a domain covering S and return carrier a subset of C. All child objects are WD.

**Common native properties and proof routes.** Empty sum zero, singleton evaluation, set partition/reindex identities, and pointwise comparison through native interfaces.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Finiteness and domain coverage are separate obligations.

**Checked example.**

```litex
finite_set_sum({}, fn(k Z) Z {k}) = 0
finite_set_sum({1, 2}, fn(k Z) Z {k}) = 3
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs); `O84` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O85. Finite-set products

**Public form:** `finite_set_product(S,f)`.

**Mathematical function.** A scalar product indexed by a finite set.

**Well-definedness and domain.** S finite; f unary with a domain covering S and return carrier a subset of C. All child objects are WD.

**Common native properties and proof routes.** Empty product one, singleton evaluation, partition/reindex identities and nonzero-factor laws.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The empty product is one; it is not an empty sum convention.

**Checked example.**

```litex
finite_set_product({}, fn(k Z) Z {k}) = 1
finite_set_product({2, 3}, fn(k Z) Z {k}) = 6
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs); `O85` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O86. Ordered folds

**Public form:** `reduce(a,b,f,op,seed)`.

**Mathematical function.** Fold iterand values through a homogeneous binary operation and initial seed.

**Well-definedness and domain.** Integer endpoints; f unary into T over the indices; op belongs to fn(x,y T) T; seed in T. All child objects are WD.

**Common native properties and proof routes.** A reversed empty range returns the seed; scalar addition folds can connect to sums.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** T is the actual homogeneous carrier; arbitrary seed/operation types cannot be mixed.

**Checked example.**

```litex
reduce(2, 1, fn(k Z) Z {k}, fn(a,b Z) Z {a+b}, 7) = 7
reduce(1, 2, fn(k Z) Z {k}, fn(a,b Z) Z {a+b}, 0) = 3
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs); `O86` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O87. Finite-set folds

**Public form:** `finite_set_reduce(S,f,op,seed)`.

**Mathematical function.** The native finite-set fold with an initial value.

**Well-definedness and domain.** S finite; f covers S and returns T; binary op is homogeneous on T; seed belongs to T. All child objects are WD.

**Common native properties and proof routes.** Empty-set fold returns seed; singleton step uses finite_set_reduce_singleton; additive folds connect to finite_set_sum.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Typing alone does not certify a chosen operation is commutative. Claims about changing enumeration need separately justified laws.

**Checked example.**

```litex
finite_set_reduce({}, fn(k Z) Z {k}, fn(a,b Z) Z {a+b}, 7) = 7
finite_set_reduce({1,2}, fn(k Z) Z {k}, fn(a,b Z) Z {a+b}, 0) = finite_set_sum({1,2}, fn(k Z) Z {k}) = 3
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs); `O87` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O88. Finite cardinality

**Public form:** `finite_set_size(S)`.

**Mathematical function.** The number of elements of a finite set.

**Well-definedness and domain.** S is proved finite.

**Common native properties and proof routes.** Natural result; empty/singleton/list size and inclusion/finite-product cardinality laws.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A set object is not automatically finite; displayed lists also require pairwise distinctness.

**Checked example.**

```litex
finite_set_size({}) = 0
finite_set_size({1,2}) = 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O88` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O89. Maximum of a finite set

**Public form:** `finite_set_max(S)`.

**Mathematical function.** The largest element of a finite nonempty real-valued set.

**Well-definedness and domain.** S finite, nonempty, and a subset of R.

**Common native properties and proof routes.** Real result, membership in S and upper-bound laws.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Neither an empty set nor an arbitrary finite complex-valued set supplies this maximum.

**Checked example.**

```litex
finite_set_max({1,3,2}) = 3
finite_set_max({1,3,2}) $in {1,3,2}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O89` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O90. Minimum of a finite set

**Public form:** `finite_set_min(S)`.

**Mathematical function.** The smallest element of a finite nonempty real-valued set.

**Well-definedness and domain.** S finite, nonempty, and a subset of R.

**Common native properties and proof routes.** Real result, membership in S and lower-bound laws.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** The binary min takes two real arguments; this operator takes a single set.

**Checked example.**

```litex
finite_set_min({1,3,2}) = 1
finite_set_min({1,3,2}) $in {1,3,2}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs); `O90` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality).

### O91. Struct carriers

**Public form:** `&Name<arguments>`.

**Mathematical function.** The carrier selected by a particular struct definition and its parameter instantiation.

**Well-definedness and domain.** The declaration owner exists, arguments match its parameter contracts, and its instantiated field/condition schema is WD.

**Common native properties and proof routes.** Membership means the exact finite coordinate structure and declared laws. Direct typed bindings open one layer; explicit struct_member introduces membership when a supported structural proof needs it.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A field name does not choose a struct owner. Qualified and template-instantiated views retain their actual definition owner.

**Checked example.**

```litex
struct Point:
    x R
    y R

(1, 2) $in &Point

struct PosPoint:
    x R
    y R
    <=>:
        x > 0

(1, 2) $in &PosPoint
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O91` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S16 Structured carriers](#s16-structured-carriers), [S27 Open one struct definition layer](#s27-open-one-struct-definition-layer).

### O92. Definition-owned field access

**Public form:** `value.field`.

**Mathematical function.** Select a named coordinate of a known struct view.

**Well-definedness and domain.** The receiver’s definition-owned struct view, membership and field must verify. Callable or nested fields retain their declared signature/view.

**Common native properties and proof routes.** Field WD makes the path legal; release struct def exposes the selected layer’s carriers, coordinate bridges and laws when needed in proof.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** A WD path does not automatically open every nested struct definition or assert every surrounding property.

**Checked example.**

```litex
struct Point:
    x R
    y R

forall p &Point:
    p.x = p.x
    p.y = p.y
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O92` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S16 Structured carriers](#s16-structured-carriers), [S27 Open one struct definition layer](#s27-open-one-struct-definition-layer).

### O93. Template instances

**Public form:** `\Name<arguments>`.

**Mathematical function.** Specialize a parameterized declaration family to concrete mathematical arguments.

**Well-definedness and domain.** The family exists and its argument carriers/guards and instantiated ordinary definition contract check.

**Common native properties and proof routes.** The instance obtains the ordinary definition’s value or callable interface; release obj def and equality/application routes use that stored definition.

**Checking and use.** Check child objects before the operation-specific requirements. Result membership is a separate usable fact; WD alone is not a proof of every property of the result.

**Nearest boundary.** Angle-bracket arguments specialize the family. Parenthesized arguments apply a fully specialized function.

**Checked example.**

```litex
template<S set>:
    have carrier_copy set = S

\carrier_copy<R> = R
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs); `O93` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S05 Typed values given by equality](#s05-typed-values-given-by-equality), [S17 Parameterized declaration families](#s17-parameterized-declaration-families), [S28 Replay an object definition](#s28-replay-an-object-definition).

## Builtin atomic fact dictionary and relationships

| ID | Public form | Mathematical role | Example status |
|---|---|---|---|
| [F01](#f01-membership-and-nonmembership) | `x $in S; not x $in S` | Membership and nonmembership | checked |
| [F02](#f02-equality-and-inequality) | `a = b; a != b` | Equality and inequality | checked |
| [F03](#f03-strict-less-than) | `a < b; not a < b` | Strict less-than | checked |
| [F04](#f04-strict-greater-than) | `a > b; not a > b` | Strict greater-than | checked |
| [F05](#f05-weak-less-than) | `a <= b; not a <= b` | Weak less-than | checked |
| [F06](#f06-weak-greater-than) | `a >= b; not a >= b` | Weak greater-than | checked |
| [F07](#f07-sethood) | `$is_set(A); not $is_set(A)` | Sethood | checked |
| [F08](#f08-nonemptiness) | `$is_nonempty_set(S); not $is_nonempty_set(S)` | Nonemptiness | checked |
| [F09](#f09-finiteness) | `$is_finite_set(S); not $is_finite_set(S)` | Finiteness | checked |
| [F10](#f10-subset) | `A $subset B; not A $subset B` | Subset | checked |
| [F11](#f11-superset) | `A $superset B; not A $superset B` | Superset | checked |
| [F12](#f12-proper-subset) | `A $proper_subset B; not A $proper_subset B` | Proper subset | checked |
| [F13](#f13-proper-superset) | `A $proper_superset B; not A $proper_superset B` | Proper superset | checked |
| [F14](#f14-primality) | `$prime(n); not $prime(n)` | Primality | checked |
| [F15](#f15-coprimality) | `$coprime(a, b); not $coprime(a, b)` | Coprimality | checked |
| [F16](#f16-divisibility-with-dividend-first) | `$dvd(a, d); not $dvd(a, d)` | Divisibility with dividend first | checked |
| [F17](#f17-injectivity) | `$injective(A, B, f); not $injective(A, B, f)` | Injectivity | checked |
| [F18](#f18-surjectivity) | `$surjective(A, B, f); not $surjective(A, B, f)` | Surjectivity | checked |
| [F19](#f19-bijectivity) | `$bijective(A, B, f); not $bijective(A, B, f)` | Bijectivity | checked |
| [F20](#f20-choice-function-specification) | `$is_choice_function_for(I, S, g, f); not $is_choice_function_for(I, S, g, f)` | Choice-function specification | checked |

| ID | Public form | Mathematical role | Example status |
|---|---|---|---|
| [C01](#c01-native-least-upper-bound-certificate) | `$is_real_least_upper_bound(A, value)` | Native least-upper-bound certificate | checked |
| [C02](#c02-native-greatest-lower-bound-certificate) | `$is_real_greatest_lower_bound(A, value)` | Native greatest-lower-bound certificate | checked |

### F01. Membership and nonmembership

**Positive form:** `x $in S`.
**Negative form:** `not x $in S`.
**Argument order:** element first, containing set second.

#### Mathematical function

Assert that an object belongs, or does not belong, to a set. A carrier
annotation such as `have n N` introduces membership information about `n`.
It does not change a host-language runtime type. Litex's pure-set model uses
one mathematical object universe, with membership as a fact between objects.

Checking WD of `x` and `S` precedes checking the membership's truth. In
particular, `1 / x $in R` must first satisfy the divisor condition even though
its target carrier is real.

#### Basic checked examples

```litex
2 $in N
-2 $in Z
not -2 $in N
1 / 2 $in Q
not 1 / 2 $in Z
```

These closed facts use `proof_method.type: by_closed_calculation` in the
verified output. Exact closed nonmembership is supported; lack of a proof of
membership is not itself a proof of nonmembership.

#### Relationships with other facts

| Available information | Consequence | How it becomes usable in these samples |
|---|---|---|
| `n $in N` | `n $in Z`, `Q`, `R`, `C` | Numeric inclusion is checked by `by_structural_membership` |
| `n $in N` | `0 <= n` | Eager inference stores the bound; the later line uses `cite_known` |
| `x $in R+` | `0 < x`, `0 <= x`, `x != 0` | Signed-carrier inference stores these facts |
| `x $in R+` | `x $in R` | Structural membership from the numeric carrier |
| Stored `0 < x` | `x > 0` | Verification uses the converse-order builtin rule |
| A checked function signature | The result of a legal call belongs to its return carrier | Callable result contract; the call's domain must still check |
| Membership in `{t R: t > 0}` | Membership in `R` and the filter `x > 0` | Set-builder membership inference stores these clauses |
| `A $subset B` and `x $in A` | `x $in B` | Inclusion exposes a universal membership implication |

The distinction between inference and verification matters. Numeric widening
such as `N` to `R` is available to structural membership checking; this is not
claimed to mean that every widened membership was eagerly stored. By contrast,
the nonnegative bound in the next example is already stored.

```litex
have n N
n $in Z
n $in Q
n $in R
n $in C
0 <= n
```

A positive real carrier also supplies the divisor guard:

```litex
have x R+
x $in R
x > 0
x != 0
1 / x $in R
```

Here `x != 0` is a stored consequence of the carrier. There is no need to add
an unrelated theorem or assume nonzeroness again. The final line checks real
membership after division WD.

#### Function-space membership

```litex
have fn square(x R) R = x^2
square $in fn(x R) R
forall t R:
    square(t) $in R
```

`have fn` has already stored the function-space membership. It makes each
legal call return an object in `R`; it does not assert that this function is
injective or surjective. Those mapping properties are separate atomic facts.

#### Set-builder membership

```litex
witness $is_nonempty_set({t R: t > 0}) from 1
have x {t R: t > 0}
x $in R
x > 0
x != 0
1 / x $in R
```

The first line establishes nonemptiness using a concrete member. `have` can
then introduce an arbitrary member. Membership in the builder exposes the
base-carrier and filter facts; strict order supports the later nonzero check.
The explicit consequence lines are retained here to show what can be read
from the membership, rather than because every one must be repeated in proofs.

#### Inclusion and membership are different fact shapes

```litex
forall A, B set, x A:
    A $subset B
    =>:
        x $in B
```

Subset relates two sets. Membership relates one object to a containing set.
An inclusion lets existing membership move in its indicated direction; it
does not identify the two sets or establish the opposite inclusion.

#### Negative boundary

**Expected rejection — phase `search_proof`:**

<!-- litex:skip-test -->
```litex
have x R
not x $in Z
```

Being real does not establish nonmembership in the integers. This failed
check also does not establish `x $in Z`. Keep an unproved goal distinct from
its negation.

**Evidence:** M01–M07.
**Source:** [atomic WD](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_well_defined.rs),
[structural membership](../src/execute/execute_fact_stmt/verify_atomic_fact/search_structural_membership.rs),
[signed-carrier inference](../src/store_fact_and_infer/infer_fact/infer_atomic_fact/infer_atomic_except_equality/membership_signed_standard_set.rs),
[builder projection](../src/store_fact_and_infer/infer_fact/infer_atomic_fact/infer_atomic_except_equality/membership_projection.rs),
[subset inference](../src/store_fact_and_infer/infer_fact/infer_atomic_fact/infer_atomic_except_equality/subset.rs).

### F02. Equality and inequality

**Public form:** `a = b; a != b`.

**Mathematical function.** Assert equality of mathematical objects, or its negation. The objects can be numeric, sets, functions or structured values.

**Well-definedness and domain.** Both objects must be WD. Equality is not limited to real scalars; ordered comparisons have their own stricter carrier requirements.

**Relationships and inference.** Equality supports symmetry, transitivity and justified congruence. Set equality is extensional; function equality can be proved by complete-domain extensionality. An inequality is not inferred merely from a failed equality search.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** A known value equality can require an explicit intermediate line before rewriting inside a larger expression; see P05.

**Checked example.**

```litex
1 + 1 = 2
1 != 2
by enumerate finite_set:
    ? forall x {1, 2}:
        x $in {2, 1}
by enumerate finite_set:
    ? forall x {2, 1}:
        x $in {1, 2}
by extension {1, 2} = {2, 1}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/README.md); `F02` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F03. Strict less-than

**Public form:** `a < b; not a < b`.

**Mathematical function.** a is strictly smaller than b.

**Well-definedness and domain.** Both operands belong to R and are WD. A negated comparison has the same carrier requirements.

**Relationships and inference.** On real operands, not a < b means a >= b. Strict order implies inequality and supports the corresponding weak order.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** General complex values are not ordered here. Multiplying or dividing an inequality needs the appropriate sign and nonzero facts; do not silently preserve its direction for negative factors.

**Checked example.**

```litex
1 < 2
not 2 < 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_well_defined.rs); `F03` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F04. Strict greater-than

**Public form:** `a > b; not a > b`.

**Mathematical function.** a is strictly larger than b.

**Well-definedness and domain.** Both operands belong to R and are WD. A negated comparison has the same carrier requirements.

**Relationships and inference.** a > b is the converse of b < a; not a > b means a <= b. The converse may be verified rather than eagerly stored in both spellings.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** General complex values are not ordered here. Multiplying or dividing an inequality needs the appropriate sign and nonzero facts; do not silently preserve its direction for negative factors.

**Checked example.**

```litex
2 > 1
not 1 > 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_well_defined.rs); `F04` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F05. Weak less-than

**Public form:** `a <= b; not a <= b`.

**Mathematical function.** a is no greater than b.

**Well-definedness and domain.** Both operands belong to R and are WD. A negated comparison has the same carrier requirements.

**Relationships and inference.** Equality and strict less-than each imply weak less-than. On reals, not a <= b means a > b; a weak nonnegative bound alone does not imply nonzero.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** General complex values are not ordered here. Multiplying or dividing an inequality needs the appropriate sign and nonzero facts; do not silently preserve its direction for negative factors.

**Checked example.**

```litex
1 <= 1
1 <= 2
not 2 <= 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_well_defined.rs); `F05` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F06. Weak greater-than

**Public form:** `a >= b; not a >= b`.

**Mathematical function.** a is no smaller than b.

**Well-definedness and domain.** Both operands belong to R and are WD. A negated comparison has the same carrier requirements.

**Relationships and inference.** a >= b is the converse of b <= a; not a >= b means a < b. Positive/negative signed carriers provide their corresponding bounds.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** General complex values are not ordered here. Multiplying or dividing an inequality needs the appropriate sign and nonzero facts; do not silently preserve its direction for negative factors.

**Checked example.**

```litex
2 >= 1
1 >= 1
not 1 >= 2
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_well_defined.rs); `F06` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F07. Sethood

**Public form:** `$is_set(A); not $is_set(A)`.

**Mathematical function.** Assert that an object is a set. Litex chooses a pure-set foundation in which every WD mathematical object satisfies sethood.

**Well-definedness and domain.** The argument object must be WD. This predicate is not a host-language runtime-type test.

**Relationships and inference.** Numerals, scalar expressions, functions, standard number sets and user-defined sets all have sethood. Membership in N or R remains a separate mathematical fact.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** not $is_set is syntactically available but no positive non-set primitive is introduced by the current pure-set model. A failed WD expression is not thereby a non-set.

**Checked example.**

```litex
$is_set(1)
$is_set(R)
$is_set(fn(x R) R {x})
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_well_defined.rs); `F07` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F08. Nonemptiness

**Public form:** `$is_nonempty_set(S); not $is_nonempty_set(S)`.

**Mathematical function.** Assert existence of at least one member, or emptiness.

**Well-definedness and domain.** S is WD. A positive introduction can use a concrete proved member with witness.

**Relationships and inference.** A positive certificate licenses arbitrary have x S. Membership implies nonemptiness mathematically; nonemptiness does not give a specified numerical witness name without a selection statement. Empty displayed sets have the negative property.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** A builder may be nonempty mathematically while cold automatic search has not established it; see P06 for an explicit witness.

**Checked example.**

```litex
$is_nonempty_set({1})
not $is_nonempty_set({})
witness $is_nonempty_set({x R: x > 0}) from 1
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_well_defined.rs); `F08` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F09. Finiteness

**Public form:** `$is_finite_set(S); not $is_finite_set(S)`.

**Mathematical function.** Assert that a set has finitely many elements, or is not finite.

**Well-definedness and domain.** S is WD; proof routes use its native construction, stored facts or explicit finiteness interfaces.

**Relationships and inference.** Finiteness licenses finite_set_size, with additional conditions for extrema. A subset of a finite set is finite; the native theorem interface is useful for explicit quantified premises. Finiteness does not imply nonemptiness.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** A set object, subset of R, or a written iteration is not a finiteness certificate by itself.

**Checked example.**

```litex
$is_finite_set({})
$is_finite_set({1, 2})
not $is_finite_set(N)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_well_defined.rs); `F09` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F10. Subset

**Public form:** `A $subset B; not A $subset B`.

**Mathematical function.** Every member of A belongs to B.

**Well-definedness and domain.** Both set objects are WD. The positive definition uses the corresponding universal membership condition.

**Relationships and inference.** Positive inclusion exposes forall x A: x in B, except a builder route can use its already projected base/filter facts. Both subset directions establish equality by extension.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** Negative inclusion means there is a counterexample; it does not make an arbitrarily selected member of A a counterexample.

**Checked example.**

```litex
{1} $subset {1, 2}
by contra:
    ? not {1, 2} $subset {1}
    2 $in {1, 2}
    impossible 2 $in {1}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F10` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F11. Superset

**Public form:** `A $superset B; not A $superset B`.

**Mathematical function.** Every member of B belongs to A.

**Well-definedness and domain.** Both set objects are WD. The positive definition uses the corresponding universal membership condition.

**Relationships and inference.** A superset B is the reversed subset relationship. It transports membership from B to A, not from A to B.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** The direction is easy to reverse when writing a forall or calling a theorem.

**Checked example.**

```litex
{1, 2} $superset {1}
by contra:
    ? not {1} $superset {1, 2}
    2 $in {1, 2}
    impossible 2 $in {1}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F11` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F12. Proper subset

**Public form:** `A $proper_subset B; not A $proper_subset B`.

**Mathematical function.** A is a subset of B and is unequal to B.

**Well-definedness and domain.** Both set objects are WD. The positive definition uses the corresponding universal membership condition.

**Relationships and inference.** Its concrete definition exposes ordinary inclusion and set inequality. Ordinary subset permits equality; proper subset excludes it.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** Negating proper inclusion does not imply proper inclusion in the opposite direction: the sets may be equal or incomparable.

**Checked example.**

```litex
by def {1} $proper_subset {1, 2}
by contra:
    ? not {1} $proper_subset {1}
    impossible {1} != {1}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F12` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F13. Proper superset

**Public form:** `A $proper_superset B; not A $proper_superset B`.

**Mathematical function.** A contains B and is unequal to B.

**Well-definedness and domain.** Both set objects are WD. The positive definition uses the corresponding universal membership condition.

**Relationships and inference.** Its definition exposes superset and set inequality; it is the reversal of proper subset.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** A larger-looking expression does not prove proper containment; both inclusion and inequality must be justified.

**Checked example.**

```litex
by def {1, 2} $proper_superset {1}
by contra:
    ? not {1} $proper_superset {1}
    impossible {1} != {1}
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F13` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F14. Primality

**Public form:** `$prime(n); not $prime(n)`.

**Mathematical function.** Assert that a natural number is prime, or not prime.

**Well-definedness and domain.** n belongs to N and is WD. The positive definition includes n >= 2 and the trial-divisor universal over the native range.

**Relationships and inference.** Closed primality can be decided by native calculation. A verified positive instance exposes its bound and trial-divisor definition. Explicit by def checks the actual definitional clauses rather than replacing them with a calculation request.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** One is not prime. An out-of-domain argument is a WD/domain issue, not a proof of negated primality.

**Checked example.**

```litex
$prime(5)
not $prime(6)
not $prime(1)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F14` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F15. Coprimality

**Public form:** `$coprime(a, b); not $coprime(a, b)`.

**Mathematical function.** Assert that the two natural arguments have greatest common divisor one.

**Well-definedness and domain.** The current predicate’s argument domains are N and N. Its positive definition contains the non-all-zero guard before the gcd equality.

**Relationships and inference.** A positive instance exposes a != 0 or b != 0 and gcd(a,b) = 1. Natural coprimality and the integer-domain gcd object have different public argument contracts.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** Do not assume this predicate accepts all signed integer pairs merely because many mathematical texts define that extension.

**Checked example.**

```litex
by def $coprime(14, 25)
not $coprime(14, 21)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F15` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F16. Divisibility with dividend first

**Public form:** `$dvd(a, d); not $dvd(a, d)`.

**Mathematical function.** Assert that a is divisible by d: d divides a. The public argument order is dividend, divisor.

**Well-definedness and domain.** a belongs to Z, d belongs to Z*, and both expressions are WD. Negative divisibility uses the same nonzero divisor condition.

**Relationships and inference.** The positive definition checks a % d = 0 and an integer multiplier witness a = k * d. A positive fact exposes those clauses for later use.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** This ordering differs from the conventional written relation d | a. A zero divisor is outside the native predicate domain.

**Checked example.**

```litex
4 % 2 = 0
witness exist a Z st {4 = a * 2} from 2
by def $dvd(4, 2)
by contra:
    ? not $dvd(5, 2)
    impossible 5 % 2 = 0
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F16` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction).

### F17. Injectivity

**Public form:** `$injective(A, B, f); not $injective(A, B, f)`.

**Mathematical function.** A unary map f from A to B maps distinct inputs to distinct outputs.

**Well-definedness and domain.** A and B are sets; f satisfies the requested unary callable signature. Equivalent carrier spellings require checked interface evidence, and all calls must be WD.

**Relationships and inference.** The definition is forall x,y A: f(x)=f(y) implies x=y. A positive fact exposes this universal; negative injectivity does not automatically select a collision pair.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** A callable signature or equality at one point does not prove injectivity. The carriers are part of the requested mapping interface.

**Checked example.**

```litex
have fn id1(x {1}) {1} = x
by def $injective({1}, {1}, id1)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F17` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction), [S01 Expression-defined functions](#s01-expression-defined-functions), [S35 Existential witnesses](#s35-existential-witnesses).

### F18. Surjectivity

**Public form:** `$surjective(A, B, f); not $surjective(A, B, f)`.

**Mathematical function.** Every value in B has a preimage under f from A.

**Well-definedness and domain.** A and B are sets; f satisfies the requested unary callable signature. Equivalent carrier spellings require checked interface evidence, and all calls must be WD.

**Relationships and inference.** The definition is forall y B: exist x A st {y=f(x)}. Prove that universal with witnesses, then fold by def; positive inference exposes the same interface.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** One existential preimage does not prove surjectivity over the whole codomain. A return bound need not equal the actual image.

**Checked example.**

```litex
have fn identity(x R) R = x
claim:
    ? forall y R:
        exist x R st {y = identity(x)}
    witness exist x R st {y = identity(x)} from y
by def $surjective(R, R, identity)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F18` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction), [S01 Expression-defined functions](#s01-expression-defined-functions), [S35 Existential witnesses](#s35-existential-witnesses).

### F19. Bijectivity

**Public form:** `$bijective(A, B, f); not $bijective(A, B, f)`.

**Mathematical function.** The requested map is both injective and surjective on the same domain/codomain.

**Well-definedness and domain.** A and B are sets; f satisfies the requested unary callable signature. Equivalent carrier spellings require checked interface evidence, and all calls must be WD.

**Relationships and inference.** Its definition is the conjunction of injective and surjective on that triple. Positive definition inference exposes the two mapping facts.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** Changing the codomain can change bijectivity even when the pointwise expression is unchanged.

**Checked example.**

```litex
have fn id1(x {1}) {1} = x
by def $injective({1}, {1}, id1)
claim:
    ? forall y {1}:
        exist x {1} st {y = id1(x)}
    witness exist x {1} st {y = id1(x)} from y
by def $surjective({1}, {1}, id1)
by def $bijective({1}, {1}, id1)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F19` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction), [S01 Expression-defined functions](#s01-expression-defined-functions), [S35 Existential witnesses](#s35-existential-witnesses).

### F20. Choice-function specification

**Public form:** `$is_choice_function_for(I, S, g, f); not $is_choice_function_for(I, S, g, f)`.

**Mathematical function.** For every alpha in I, f(alpha) is a member of the selected family set g(alpha).

**Well-definedness and domain.** I and S are sets; g satisfies fn(alpha I) S and f satisfies fn(alpha I) family_union(S). Both callable contracts are independent WD requirements.

**Relationships and inference.** The pointwise membership universal is the defining clause. Choice releases produce existential facts with this atomic specification; obtain is needed to name the chosen function.

**Checking and use.** Check argument-object WD and predicate-domain requirements, then the supported known/calculation/verification/definition route. Store a successful fact and only its applicable inference; negative forms do not inherit positive definition expansion.

**Nearest boundary.** An arbitrary function returning into family_union(S) is not necessarily a choice from each particular g(alpha). Carrier equivalence must be checked for both signatures.

**Checked example.**

```litex
have fn family(alpha {1}) power_set({1}) = {1}
have fn choice(alpha {1}) {1} = 1
forall alpha {1}:
    choice(alpha) $in family(alpha)
by def $is_choice_function_for({1}, power_set({1}), family, choice)
```

**Source and evidence:** [implementation](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/builtin_prop_definition.rs); `F20` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [F01 Membership and nonmembership](#f01-membership-and-nonmembership), [S02 Bare factual statements](#s02-bare-factual-statements), [S47 Explicit definition folding](#s47-explicit-definition-folding), [S40 Proof by contradiction](#s40-proof-by-contradiction), [S01 Expression-defined functions](#s01-expression-defined-functions), [S35 Existential witnesses](#s35-existential-witnesses).

### C01. Native least-upper-bound certificate

**Public form:** `$is_real_least_upper_bound(A, value)`.

**Mathematical function.** The opaque native certificate that value is the supremum of A.

**Well-definedness and domain.** The reserved predicate signature has arity two. Its genuine mathematical evidence comes from the corresponding checked completeness release, whose subset, nonempty and bound hypotheses must verify.

**Checking and use.** The native existence theorem produces an existential certificate. Companion native theorem interfaces use it to project member/bound inequalities.

**Nearest boundary.** Recognizing this builtin signature does not prove any instance or supply a user-editable concrete prop body.

**Checked example.**

```litex
release thm real_least_upper_bound_exists({0}, 1)
exist L R st {$is_real_least_upper_bound({0}, L)}
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/builtin_thm/real_analysis.rs); `C01` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [S25 Publish theorem conclusions](#s25-publish-theorem-conclusions), [S07 Extract existential witnesses](#s07-extract-existential-witnesses).

### C02. Native greatest-lower-bound certificate

**Public form:** `$is_real_greatest_lower_bound(A, value)`.

**Mathematical function.** The opaque native certificate that value is the infimum of A.

**Well-definedness and domain.** The reserved predicate signature has arity two. Its genuine mathematical evidence comes from the corresponding checked completeness release, whose subset, nonempty and bound hypotheses must verify.

**Checking and use.** The native existence theorem produces an existential certificate. Companion native theorem interfaces use it to project member/bound inequalities.

**Nearest boundary.** Recognizing this builtin signature does not prove any instance or supply a user-editable concrete prop body.

**Checked example.**

```litex
release thm real_greatest_lower_bound_exists({0}, -1)
exist L R st {$is_real_greatest_lower_bound({0}, L)}
```

**Source and evidence:** [implementation](../src/execute/execute_by_stmt/builtin_thm/real_analysis.rs); `C02` in the [inventory and verification record](audits/reference-inventory-2026-10-06.json).

**Related entries:** [S25 Publish theorem conclusions](#s25-publish-theorem-conclusions), [S07 Extract existential witnesses](#s07-extract-existential-witnesses).

## Pitfalls and missing proof steps

Each card pairs an exact rejection with an appropriate positive example or a
linked correction. Error-phase labels below are taken from isolated current
runs. A mathematical counterexample, missing premise, and proof-search miss
are different reasons; each card states which applies.

### P01. Reflexivity does not bypass well-definedness

**Intention:** assert the reflexive equality of a reciprocal expression.
**Expected rejection — phase `well_defined`:**

<!-- litex:skip-test -->
```litex
have x R
1 / x = 1 / x
```

The checker stops before comparing the two sides: `x != 0` is unavailable.
Writing identical expressions does not make an undefined division legal.
The positive counterpart is the guarded universal in
[O01](#domain-and-well-definedness), with the same reflexive goal for inputs
in its actual domain. For a callable construction, use the next card.

### P02. The body must be meaningful throughout the function domain

**Expected rejection — phase `have_fn_equal`; anonymous-function body WD fails:**

<!-- litex:skip-test -->
```litex
have fn reciprocal(x R) R = 1 / x
```

The declared domain includes zero. The repair for the intended partial
reciprocal is the guarded definition in [S01](#parameters-domain-and-return-set).
This is a domain correction, not proof automation. If the intended mathematics
requires a value at zero, a different definition specifying that value is needed.

### P03. A legal function declaration does not license every call

**Expected rejection — phase `well_defined`:**

<!-- litex:skip-test -->
```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(0) = 0
```

The call violates the written guard. Changing the right side of the equation
cannot repair its argument domain. The positive calls at `2` and `-2` in S01
satisfy the signature.

A guard also does not establish any desired equation involving the expression.
**Expected rejection — phase `search_proof`:**

<!-- litex:skip-test -->
```litex
forall x R:
    x != 0
    =>:
        1 / x = 1
```

The expressions are WD, but the mathematical universal is false; `x = 2` is
a counterexample. Nonzeroness and the value of the reciprocal are independent
questions. This example must not be diagnosed as another missing WD guard.

### P04. Connect division and multiplication explicitly

**Intention:** from `a / b = c` and `b != 0`, deduce `a = c * b`.
**Expected rejection — phase `search_proof` in this cold context:**

<!-- litex:skip-test -->
```litex
forall a, b, c R:
    b != 0
    a / b = c
    =>:
        a = c * b
```

The mathematics is valid. In the current checker, this bare goal does not
find the route by itself. A checked proof keeps the same hypothesis and target:

```litex
claim:
    ? forall a, b, c R:
        b != 0
        a / b = c
        =>:
            a = c * b
    a = (a / b) * b = c * b
```

The chain has two mathematical steps: `(a / b) * b = a` uses division
cancellation, and replacing `a / b` by `c` uses the premise. Its middle
expression connects an implemented identity to a known equality.
The proof uses the active goal parameters `a`, `b`, `c`; it does not introduce
a second universal with renamed parameters inside the proof body.

The reverse direction has the corresponding boundary.
**Expected rejection — phase `search_proof`:**

<!-- litex:skip-test -->
```litex
forall a, b, c R:
    b != 0
    a = b * c
    =>:
        a / b = c
```

Checked counterpart:

```litex
claim:
    ? forall a, b, c R:
        b != 0
        a = b * c
        =>:
            a / b = c
    a / b = (b * c) / b = c
```

Removing the equality-chain body from either `claim` was independently tested
and rejected. These are current proof-search boundaries, not additional
mathematical hypotheses or claims that every algebraic proof needs a `claim`.

### P05. A function equation may need to be exposed before substitution

The complete reciprocal-law proof is in [R01](#prove-a-law-of-the-function).
It contains these two mathematical steps:

<!-- litex:skip-test -->
```litex
# Fragment of the full checked R01 proof; x and reciprocal are defined there.
reciprocal(x) = 1 / x
reciprocal(x) * x = (1 / x) * x = 1
```

The first line establishes the specific function value equality. The second
uses it under multiplication and closes the scalar identity. In the current
checked context, a direct universal goal fails; deleting the first line while
retaining the chain also fails. Retaining only the first line fails to close
the law. The full two-step proof passes.

This boundary concerns the exact reciprocal-law example. It does not mean
that every function application needs a manually repeated defining equation.
Concrete evaluations such as `reciprocal(2) = 1 / 2` already verify directly.

### P06. Arbitrary `have` needs nonemptiness

**Expected rejection — phase `have_in_nonempty`:**

<!-- litex:skip-test -->
```litex
have x {t R: t > 0}
```

In this cold context, the checker has not established that this builder is
nonempty. It does not follow that the set is empty. The correction in
[F01](#set-builder-membership) supplies `1` as a concrete member using
`witness`, then introduces an arbitrary member with `have`.

A builder's definition, an established member, and an arbitrary selection
are different steps. Do not append uses of `x` after a failed declaration:
that name was not successfully introduced, so a later line has an earlier
name-resolution problem to fix first.

## Recommended mathematical formulations

### R01. Define and use a reciprocal function

**Ordinary mathematics:** a function on nonzero reals, returning `1 / x`.

**Recommended form:** the guarded expression-defined function from S01:
`have fn reciprocal(x R: x != 0) R = 1 / x`.
The signature states the domain where the expression is meaningful, and the
return carrier states the output contract. Callers can see their obligation
without inspecting the definition body.

**Supported alternative:** use the nonzero-real carrier `R*`:

```litex
have fn reciprocal(x R*) R = 1 / x
reciprocal(2) = 1 / 2
```

`R*` carries real membership and nonzeroness. Both definitions express the
same intended mathematical domain here. The explicit guard spells out the
condition for readers learning WD; the carrier form is useful when the domain
already plays a recurring role. The current public spellings include `R+`
and `R*`; do not infer aliases such as `R_pos` from old notes.

### Prove a law of the function

**Ordinary mathematics:** the reciprocal multiplied by its nonzero argument
is one. Define the callable value, expose its equation at the active argument,
then use the division identity:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
claim:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1
```

This example demonstrates the full route through the dictionaries:

1. [S01](#s01-expression-defined-functions) gives the definition and stored
   callable contract.
2. [O01](#o01-division) explains the guard and the scalar identity.
3. [F01](#f01-membership-and-nonmembership) explains carrier information and
   legal function applications.
4. [P05](#p05-a-function-equation-may-need-to-be-exposed-before-substitution)
   explains the two explicit steps needed by this proof.

The proof machinery remains local to the `claim`; the successful statement
exports its universal conclusion. No helper theorem merely restating the
function definition is introduced.

### R02. Choose the language form by mathematical role

| Mathematical intention | Recommended form | Why |
|---|---|---|
| A named callable value given by a formula | `have fn ... = ...` | Later code needs to apply the function and use its return contract |
| A condition on an object | `prop ...` | Names a mathematical proposition with a concrete definition |
| A one-off derived fact requiring intermediate steps | `claim` | Proves and exports the goal while keeping helpers local |
| A routine carrier consequence | State the membership directly | Use the existing carrier machinery without an unnecessary wrapper |
| A division transformation whose cold goal misses | A local equality chain as in P04 | Connects the original expression to the usable identity |
| A reusable mathematical result | A named `thm` interface | Worth naming when later developments need that result |

These are recommendations about roles and proof organization, not a list of
new parser restrictions. Distinguish a mathematical domain requirement from
a source-style choice. For example, multiline `forall` is the recommended
teaching form; the supported inline syntax is not made invalid by that choice.

## Verification and coverage

All dictionary categories have stable entries and source ownership. This
edition distinguishes 51 public statement forms, 93 active object leaves,
20 dedicated builtin atomic families (with their negative counterparts), and
two native certificate predicates. Public aliases share the relevant entry;
the witness/unique-witness distinction is counted as separate statement forms.

The positive runnable fences are self-contained. Most run in strict mode;
assumption demonstrations run in ordinary mode and are explicitly rejected
under strict mode. Expected negative examples are tested separately and skipped
by the positive Markdown collector. The contextual two-line reciprocal fragment
is verified inside the full R01 example, not executed without its binders.

Acceptance uses current-source release CLI Normal JSON: exit 0, `kind: run`,
`success: true`, and no session error. Old `-compact`, `-runner`, `-before`,
`-isolated` and literal `try:` recipes do not apply to this build. Prototype
boundaries and corrected code are retained in the inventory journal; a failed
search is never counted as a proof of the opposite fact.

The original [sample evidence](audits/reference-samples-2026-10-06.json) is a
historical checkpoint. The [current inventory and evidence](audits/reference-inventory-2026-10-06.json)
owns this expanded edition. Object-property families have source-reviewed
conditions and executed representative cases. This is not an exhaustive list
of every instantiated equality, every kernel rule ID or every imported theorem.

The current Normal `statement` rendering of expression-defined functions
omits the written return carrier. Original fenced source is retained for
interpretation of return-bound failures. Source facts, execution evidence and
user assumptions remain distinct throughout the entries.

# Litex System Map

Litex is easiest to understand as a sequence of checked context updates. Each
statement reads the context produced by earlier statements and performs its own
checks. If its target succeeds, it commits the binding, definition, or fact
specified by that statement.

*Visit https://litexlang.com/doc/Manual for more detailed explanation of Litex kernel implementation.*

```text
Object -> Fact -> Statement -> growing proof context
```

This page describes the stable, author-facing execution model. It is not an
exhaustive token glossary or a specification of kernel internals. The contract
here is what an author needs to predict the scope, proof obligations, context
effects, and direct trust boundaries of ordinary Litex code.

For runnable syntax examples, start with [Litex Examples](Examples.md#start-here).
For a denser executor reference, use the
[Statement Execution Cheat Sheet](cheatsheet.md). The
[FAQ](FAQ.md#why-does-litex-think-of-proof-as-context-growth) gives more
motivation for the context-growth model.

## A Checked File in Miniature

```litex
have x R = 2

x + 1 = 3
x^2 = 4
```

The first statement checks that `2` is a real number, binds `x`, and records
both `x $in R` and `x = 2`. The next statement is checked from that context.
After it succeeds, `x + 1 = 3` is also available to the final statement.

This small file already shows the main Litex loop:

1. Read the next mathematical statement.
2. Check that every object in it is meaningful.
3. Find a verification route from the current context.
4. Store the accepted result.
5. Infer routine consequences.
6. Continue with a larger context.

## The Four Layers

| Layer | Example | Runtime role | Context effect by itself |
|---|---|---|---|
| **Object** | `x + 1`, `R`, `f(x)` | A mathematical expression. Object well-definedness includes name resolution, domains, types, and side conditions of partial operations. | None. An object must occur in a fact or defining statement to affect the context. |
| **Fact** | `x + 1 = 3`, `x $in R`, `$P(x)` | A proposition that can be well-defined, true, or not currently established. | None while merely nested. A fact used as a statement is checked and, on success, stored. |
| **Statement** | `have`, a bare fact, `claim`, `thm`, `witness`, `by cases` | An action with structural checks, proof obligations, and a specified commit effect. | Depends on the statement. Some commit in the current scope, some release only a proved target, and some discard their local work. |
| **Context** | Known names, definitions, facts, theorem interfaces, and inferred consequences | The mathematical state visible to the next statement in the current scope. | A statement's documented result enters the context only after that result succeeds or is explicitly trusted. |

A statement can be successful without adding a fact. For example, `prop`
stores a definition, `have algo` stores an executable implementation, and
`sketch` deliberately exports nothing.

## One Statement Lifecycle

The common execution shape is:

```text
parse
  -> select the current or a child scope
  -> structural and well-definedness checks
  -> verification or generated subgoals
  -> commit names, definitions, or accepted facts
  -> infer routine consequences of those committed results
  -> report the result
```

Not every statement uses every phase. A definition may have no truth claim to
prove. A proof block creates child scopes. `sketch` never commits its child
scope. `trust` and `axiom` deliberately skip truth verification, but remain
explicit trust boundaries and are rejected in strict mode.

For the target of a checked fact, the important ordering rule is:

```text
verify target -> commit accepted target -> infer from that target commit
```

Well-definedness may itself record mechanically justified supporting type or
application facts. It does not store the target as proved. Once the target
verifies, Litex stores it and runs its post-verification inference. An inferred
consequence can justify a later statement, but it is not the route that
justified the statement whose successful storage triggered that inference.

## Scope and Release

Local proof work is isolated from the surrounding context. A construct decides
which assumptions enter its child scope and which result, if any, is released
back to its parent.

| Construct | What enters the local scope | What leaves it |
|---|---|---|
| Top-level sequence | Everything committed by earlier top-level statements. | Each successful committing statement extends the file context. |
| `forall` | Fresh arbitrary parameters, their type facts, and the stated premises as assumptions. | Only the verified universal fact. Parameter names and assumed premises do not escape. |
| `exist` / `exist!` fact | Bound witness variables exist only inside the fact body. | The existential fact, not a usable witness name. |
| `claim` | A child of the current context. For a universal goal it also receives the universal parameters and premises. | The proved target fact. Intermediate proof bindings and facts are discarded. |
| `thm` | A child scope containing theorem parameters and premises. | The named theorem interface and its verified universal fact. |
| `by cases` | One independent child scope per case, with that case assumed. | The common target facts, after coverage and every branch have been checked. |
| `by contra` | A child scope with the logical negation of the target assumed. | The original target, after an explicit contradiction is verified. |
| Induction and finite iteration | Separate base, step, or assignment scopes with the appropriate local hypotheses. | The resulting universal target. |
| `sketch` | A child of the current context. | Nothing. All nested bindings and facts are discarded. |
| `try` | A child of the current context. | The whole child environment, but only when every nested statement succeeds. |
| `have` / `obtain` | No disposable proof scope after their obligations close. | New names and their associated facts in the current scope. |

An existential fact therefore does not silently expose a globally named
witness. Use `witness` to prove an existential and `obtain` to introduce opaque
witness names from an existential that is already known.

## How Fact Shapes Run

Compound facts are not all handled in the same way. Their logical shape
determines which local assumptions or subgoals Litex creates.

| Fact shape | Verification meaning | Context effect after success |
|---|---|---|
| Atomic fact, such as `x = y`, `x $in S`, or `$P(x)` | Check object well-definedness, then seek evidence through the atomic verification loop below. | Store the atomic fact and run its inference routines. |
| Chain, such as `0 <= x <= 1` | Expand the chain into its adjacent atomic relations and verify every step. | Make the component relations, and supported chain consequences, available. |
| Conjunction, such as `A and B` | Verify every component. Failure of one component fails the conjunction. | Store the component facts; each can be reused independently. |
| Disjunction, such as `A or B` | Establish at least one branch, reuse an already known disjunction, or close the whole disjunction through a matching rule. | Store the disjunction. It does not make an unproved branch available. |
| `exist x S st {...}` | Establish existence through an explicit witness, a known existential, a known universal result, or a builtin mathematical route. | Store existence only. It does not bind `x` outside the fact. |
| `exist! x S st {...}` | Establish both existence and uniqueness. An explicit `witness exist!` must discharge the uniqueness obligation as well as the body. | Store unique existence and expose its routine uniqueness consequence. |
| `not exist x S st {...}` | Establish nonexistence as a fact, usually from known facts or an explicit proof route. | Store nonexistence and any representable routine logical consequence. |
| `forall x S: premises =>: conclusions` | In a child scope, bind arbitrary `x`, assume the premises, and verify every conclusion. | Store a reusable universal rule. Local parameters and premises disappear. |
| `forall ... <=> ...` | Convert the equivalence into two universal directions and verify both. | Store both directions for later matching. |
| `not forall ...` | Establish the negation of the universal fact, often with an explicit contradiction proof. | Store the negated universal fact and any representable counterexample consequence. |

### The Atomic Verification Loop

Most proof obligations eventually ask for an atomic target. The public model is:

```text
atomic target
  -> all objects are well-defined
  -> match a known non-forall atomic fact, or
  -> try one builtin mathematical rule, or
  -> run a strictly structural builtin strategy, or
  -> for equality at outer round 0, recursively compare matching object constructors, or
  -> verify a concrete definition at outer round 0, or
  -> match the conclusion of an applicable known forall and verify its premises, or
  -> run a user-defined strategy
  -> true or unknown
```

**Builtin mathematical patterns.** The target shape is matched against
implemented arithmetic, equality, order, membership, set, function, and
composite-object rules. A builtin rule has depth one: its premises use known
non-`forall` facts or deterministic computation and cannot invoke another
rule. Builtin strategies are a separate route for strictly smaller structural
children; each layer may try one fresh direct rule before repeating only that
strategy. Neither route enters the full verifier, known `forall` matching,
definitions, or user strategies, and the child result tree is returned to the
root.

Finite-product equality uses this split directly: pointwise congruence is a
structural strategy, while pointwise multiplication and substitution along an
already-known bijection are narrow direct rules.

A direct rule may consume several already-known premises for one fixed
mathematical implication. The natural-predecessor rule, for example, consumes
`n $in N` and `n > 0` to prove `n - 1 $in N`; it does not recursively derive
another order fact first.
Known `n $in N+` directly proves the natural result `n - 1 $in N`. The
strict-positive result additionally consumes `n > 1` to prove
`n - 1 $in N+`.
Finite-range aggregation follows the same bounded design. Equality of two
`sum` objects with common bounds may consume a guarded pointwise equality on
that exact integer range. Integer-shift reindexing may consume the analogous
guarded equality on the target range; it normalizes a constant bound shift but
does not search for arbitrary reindexing maps.
Integer adjacency is another direct one-step rule: known integer objects and
`a < b + 1` prove `a <= b`, without recursively deriving an intermediate
shifted comparison.
Integer `range` and `closed_range` objects likewise expose a direct standard
carrier edge: they lie in `Z`, and a lower endpoint already in `N` or `N+`
proves the corresponding natural subset. The finite-set strategy treats a
set-builder as a filtered subset of its base, so finiteness recurses only to
that base.

Definition-facing structural strategies are also bounded: dependent tuple
constructors are checked field by field; callable struct fields project through
one checked constructor; and set-builder membership unfolds one literal, one
checked function/template definition, or one exact indexed named-builder
equality. The indexed route does not scan the environment for approximate
aliases.

For known integers, the two singleton-interval rules retain both explicit
bounds: `n <= x < n + 1` gives `x = n`, and `n < x <= n + 1` gives
`x = n + 1`. Function extensionality can consume an exact cached pointwise
universal only when both declared function carriers are alpha-equivalent.

Known equality candidates may replay one checked function body against simple
arithmetic. Known-only equality first checks identity, direct lookup/calculation,
or an already stored equality class, then reuses one central constructor matcher
for congruence whose leaves must be known equalities. At outer round 0, the full
equality route reuses that matcher while recursively allowing bounded builtin
and known-equality child proofs. Function applications align trailing argument
groups and then compare their remaining function prefixes, so the two sides
need not have the same number of curried application groups. Other atomic-fact
lookup may use known-only congruence for transport, but does not start the fuller
child-proof route.
The nonzero rules also include `x > 0 => sqrt(x) != 0`, but not the invalid
weakening from `x >= 0`.

**Known atomic facts.** Litex looks for the same predicate and truth value in
the visible context. Arguments need not be textually identical: known
equalities can make two arguments match. For example, a known `$P(a)` may close
`$P(b)` when the context also establishes `a = b`.

**Concrete definitions.** A concrete `prop` gives Litex defining clauses for
the predicate. At outer round 0, ordinary atomic verification instantiates the
definition and verifies all clauses with the full verifier before known
`forall` matching or user strategies. `by def $P(args)` requests the same
mathematical direction explicitly and rechecks it even when `$P(args)` is
already known. Supported builtin definitions use the same statement, including
`by def A $subset B` and `by def $injective(A, B, f)`.

**Known universal facts.** Suppose the context contains:

```text
forall x S:
    A(x)
    =>:
        B(x)
```

To prove `B(t)`, Litex matches the conclusion and obtains the substitution
`x := t`. It then checks the parameter domain and verifies `A(t)`. Those
premises are ordinary full-verifier goals and can use builtin rules, known
facts, or other known universal facts. A mathematical-definition step is
tried earlier for an ordinary positive concrete predicate, or may be requested
explicitly with `by def`.

For a grouped universal declaration, each positive conclusion is also stored
over just the parameters it uses when the omitted parameter types are
independent and known nonempty. Thus a law written under
`forall a, b R, x, y E` can expose its `a, x` clause without inventing values
for `b` or `y`; the projection is deliberately unavailable when an omitted
domain may be empty.

Pattern matching is therefore shared by builtin routes, known-fact reuse, and
universal instantiation. A named `thm` also stores its universal fact, while
`by thm` provides an explicit theorem-instantiation route.

For a two-branch atomic disjunction, the verifier may use classical
implication packaging: to establish `not A or B`, temporarily assume `A` and
verify `B`. The temporary case and anything inferred only inside it do not
escape the local environment.

## Stable Statement Execution

The tables below describe the stable core statements. "Commit" means an effect
visible in the parent/current scope after the statement succeeds. "Trust
boundary" distinguishes checked work from declarations that deliberately add
unproved content. The runtime records direct trusted statement forms, but does
not persist or propagate trust metadata through later facts and theorems.

### Facts, Objects, and Definitions

| Form | Local scope | Structural / well-definedness checks | Verification / subgoals | Commit on success | Trust boundary |
|---|---|---|---|---|---|
| Bare `fact` | Determined by the fact shape. | Every object and binder must be well-defined. | Verify using the fact-shape and atomic loops. | Store the accepted fact or its reusable components, then infer. | Adds no new trust. |
| `have x S` | Introduces `x` in the current scope only after checks pass. | `x` must be unused; `S` must be well-defined. | Prove that `S` is nonempty. | Bind `x`, store `x $in S`, then infer. | Checked object introduction. |
| `have x S = value` | The defining value is checked before `x` is committed. | Name, type, and value must be well-defined. | Prove `value $in S`. | Bind `x`; store its type/membership and `x = value`; then infer. | Checked definition. |
| `have x S: body` | Uses an existential binder while checking the obligation. | The corresponding `exist x S st {body}` must be well-defined. | Prove that corresponding existential fact. | Bind an opaque witness `x`; store its type and instantiated body facts; then infer. | Checked existence, not unrestricted witness creation. |
| `obtain names from exist ...` | Opens existential binders into the current scope. | Witness count, parameter types, and existential shape must match. | Verify the source existential fact from the current context. | Bind opaque witness names and store the instantiated direct body facts; positive concrete predicate bodies recursively expose their positive clauses under cycle guards. | Adds no new trust. |
| `prop P(params): clauses` | Parameters are local while the definition is checked. | Name, parameter domains, and clauses must be well-defined. | The clauses are not proved; they declare the meaning of `P`. | Store the concrete predicate definition. | A definition, not a theorem or assumption about existing objects. |
| `abstract_prop P(params)` | Parameters describe an interface only. | Name and parameter shape must be valid and nonconflicting. | None. There is no defining body. | Store the predicate symbol and arity. | Introduces no fact; later properties still need proof or explicit trust. |
| `have fn f(params) T = body` | Parameters and domain conditions are local. | Signature, domain conditions, return set, and body must be well-defined. | Check the body has return type `T` under the parameter assumptions. | Store `f`, its function type, defining equation, and callable body facts. | Checked mathematical definition. |
| `have fn f(...) T by cases` | Each case is checked under its own local condition. | Signature, cases, conditions, and return expressions must be well-defined. | Prove coverage, mutual exclusivity, and return membership for every case. | Store the function and the case-specific universal equations. | Checked mathematical definition. |
| `have fn f(...) T by induc ...` | Base and recursive cases receive induction-local bindings. | Signature, measure, lower bound, cases, and recursive calls must have valid shapes. | Check the lower bound, coverage, return membership, and strict decrease of recursive calls. | Store the recursive function definition and its usable equations. | Checked definition with termination obligations. |
| `have fn f by exist!` | Its proof, when supplied, runs in a child scope; template materialization substitutes through local `obtain`, `witness`, equal-object and function definitions, case, and extension statements. | The source must have the expected parameterized unique-existence shape. Refined function-space return carriers remain callable after materialization. | Verify the source `forall ... exist! ...` fact or its proof block. | Store the selected function, its type, defining property, uniqueness fact, and materialized local proof consequences. | Checked use of unique existence. |
| `have algo for f(params)` | Implementation parameters and cases are local. | `f` must already be a function; parameters must match its mathematical signature. | Check each executable result and case against the established function facts. | Attach executable data used by `eval`; do not replace the mathematical definition. | Adds no mathematical assumption. |
| `eval expression` | None. | The expression must be supported and evaluable. | Compute the supported value; there is no separate proof of the resulting equality. | Report and store `expression = value`. | No user trust; the evaluator is part of the implementation's trusted surface. |

### Proofs, Theorems, and Trust

| Form | Local scope | Structural / well-definedness checks | Verification / subgoals | Commit on success | Trust boundary |
|---|---|---|---|---|---|
| `claim: ? target ...` | Proof steps run in a child scope; a universal target also opens parameters and premises there. | The target must be well-defined. `claim` does not accept a universal equivalence target. | Execute the proof, then verify the target or all universal conclusions. | Store the target and infer in the parent scope. | Checked; any explicit trusted step remains visible as its own statement result. |
| `thm name: ? forall ...` | Theorem parameters and premises live in a child proof scope. | The name must be unused and the universal statement well-defined. | Execute the proof and verify every conclusion. | Store the named theorem and its universal fact. | The theorem itself carries no transitive trust tag; direct trusted proof steps remain separately countable. |
| `axiom name: ? forall ...` | No proof scope is needed. | The named universal statement must be well-defined. | No truth proof. | Store a named theorem-like interface and universal fact. | Explicit axiom; rejected in strict mode. |
| `trust facts` | Current scope. | In user code, every assumed fact must still be well-defined and storable. | No truth proof. | Store the facts as unsafe assumptions and run inference. | Explicit proof debt; rejected in strict mode. |
| `trust have ...` | Current scope. | Bindings, types, and attached facts must be valid enough to store. | No truth proof of the attached facts. | Store names, type facts, attached assumptions, and inferred consequences. | Explicit proof debt; rejected in strict mode. |
| `sketch: ...` | All nested statements run in a child scope. | Each nested statement performs its normal checks. | Nested proof obligations run normally. | Nothing. The outer context is unchanged. | Any nested trust remains visible in the result but is not exported. |
| `try: ...` | All nested statements run in a child scope. | Each statement performs normal checks; controls that cannot be merged are rejected. | Every step must succeed; `unknown` aborts the block. | Commit the complete child environment atomically. | Inherits any trust used by committed nested statements. |
| `witness exist ... from values` | Existential parameters are locally equated with the proposed values. | Witness count, values, types, and existential body must be well-defined. | Check witness types and every instantiated body fact; `exist!` also checks uniqueness. | Store the existential fact and infer. Witness parameter names do not escape. | Checked witness proof. |
| `witness $is_nonempty_set(S) from value` | The proposed value is checked locally. | `S` and `value` must be well-defined. | Prove `value $in S`, or the corresponding supported function-set condition. | Store nonemptiness and infer. | Checked witness proof. |

### Explicit Proof Routes

Each route below generates or checks subgoals. Those subgoals return to the
same fact and atomic verification loops; a proof route is not a second,
unrelated verifier.

| Form | Local scope | Structural / well-definedness checks | Verification / subgoals | Commit on success | Trust boundary |
|---|---|---|---|---|---|
| `by def fact` | No persistent child scope. | The target must be a concrete positive prop or supported positive builtin definition. | Verify every defining requirement with the full verifier, even if the target is already known. | Store the target and infer only after all requirements succeed. | Checked use of a definition. |
| `by thm name(args)` | The instantiation is checked against the current scope. | A user theorem must exist and match its arguments; a reserved builtin theorem checks fixed arity and target shape. | Verify theorem domains or explicit builtin requirements with the full verifier. | Store conclusions and infer only after all checks succeed. | Builtin names remain bare and globally reserved; detailed output identifies `builtin_rule` source and any provenance. |
| `by cases` | One child scope per case. | Target, cases, and branch shapes must be well-defined. | Prove the cases are exhaustive, then prove every target in every branch. | Store the common target facts and infer. | Checked case analysis. |
| `by contra` | A child scope assumes the logical negation of the target. | The target must support logical negation and be well-defined. | Execute the proof and verify both a stated impossible fact and its negation. | Store the original target and infer. | Checked contradiction proof. |
| `by induc` / `by strong_induc` | Separate base and step scopes with ordinary or strong induction hypotheses. | Parameter, starting point, target, and induction shape must be valid. | Verify base and step obligations. | Store the resulting universal fact and infer. | Checked induction. |
| `by induc P:` (finite-set induction) | Separate empty/base and insertion-step scopes. | The finite-set parameter and goal shape must be valid. | Verify the base and element-adjoining step. | Store the resulting universal fact and infer. | Checked induction. |
| `by extension` | Element arguments and subset directions are checked in local scopes. | Both sides must be well-defined sets of the supported shape. | Prove both inclusion directions. | Store set equality and infer. | Checked extensionality proof. |
| `by enumerate finite_set` | One child assignment for each displayed element. | The finite set and universal target must have the expected finite shape. | Verify the target for every assignment. | Store the universal fact and infer. | Checked finite proof. |
| `by enumerate range` / `by closed_range as cases` | No proof facts escape beyond the generated result. | Membership and integer endpoints must be well-defined. | Verify the membership prerequisites and expose the corresponding equality cases. | Store the generated equality or disjunction. | Checked range expansion. |
| `by for` | One child assignment per supported finite iteration value. | Iteration domain and universal target must be well-defined and finite in the supported form. | Verify the target for every assignment. | Store the universal fact and infer. | Checked finite iteration. |

## Context Growth as a Closed Loop

```text
current context
    |
    v
next statement
    |
    v
well-definedness and verification
    |
    v
accepted fact or definition
    |
    +--> store
           |
           +--> infer routine consequences
                    |
                    v
               larger context
                    |
                    +--> next statement
```

Three distinctions matter:

1. **Verification closes the current obligation.** It explains why the target
   follows from the context or a selected proof route.
2. **Storage makes the accepted result reusable.** Conjunctions and chains may
   expose reusable component facts; universal facts become matching rules.
3. **Inference runs after storage.** It adds routine consequences such as type,
   membership, equality, order, or logical consequences supported by the
   stored fact's shape.

Inside a child proof scope the same loop still runs, so intermediate facts can
help later steps in that proof. When the scope closes, only the construct's
specified result is released.

## Reading Results and Trust

| Result | Meaning | Context consequence |
|---|---|---|
| `true` | The statement was structurally valid, its objects were well-defined, and its required verification route or declaration action succeeded. | The statement's documented commit effect occurs, followed by inference where applicable. |
| `unknown` | The verifier found the target meaningful but could not establish it from the visible context and supported routes. This does not mean false. A bare top-level fact surfaces this as a verification failure whose reason is `unknown`, not as a successful statement. | The target is not committed as a proved fact. Add a missing premise, equality, witness, case, or intermediate result. |
| `error` | Parsing, name resolution, statement shape, scope, or well-definedness failed, or a proof block violated its execution contract. | The failed target is not committed as a verified result. Supporting facts produced while checking well-definedness may already be present; general statement failure is not a rollback promise. |
| Direct trusted statement | The source explicitly uses `axiom`, `trust`, `trust have`, or another trusted proof form. This is a statement classification, not a fourth truth value. | The declared fact can enter the context. Strict mode rejects the source-level trusted form; later results are not transitively tagged by the runtime. |

A useful explanation separates:

```text
verified by ...      why the target was accepted
store ...            what entered the context
infer ...            what was added after that storage
direct trust count ... which explicit trusted statement forms occurred
```

Definition-graph output may analyze direct trusted syntax and graph edges at
graph-generation time. That reporting analysis is separate from Runtime
execution and does not require trust fields in the environment. Litex proofs
are controlled, scope-aware updates to a growing mathematical context.

## Boundary of This Map

This map intentionally commits only to stable observable behavior. Kernel
search and scheduling details are not part of the author contract and may
change without changing Litex source meaning. A kernel-level manual should
document deeper mechanisms separately when their design and disclosure
boundary are settled.

Finite-natural maximum existence is a shape-restricted existential builtin:
it recognizes a concrete definition consisting of witness membership and one
universal upper-bound clause, then requires direct finite, nonempty, and
subset-of-`N` premises. Concrete proposition folding similarly tries bounded
argument-type evidence and exact cached definition clauses before any broader
search. Both routes are intentionally local; neither scans arbitrary
proposition definitions for approximate matches.

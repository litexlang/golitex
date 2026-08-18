# Litex System Map

> **Litex is an experimental hobby project still in beta. Expect rough edges.**

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
`example` and `sketch` deliberately export nothing.

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
prove. A proof block creates child scopes. `example` and `sketch` never commit
their child scopes. `trust` and `axiom` deliberately skip truth verification,
but remain explicit trust boundaries and are rejected in strict mode.

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
| `example` | A child of the current context. For a universal goal it also receives the universal parameters and premises. | Nothing. The checked target, parameters, premises, and proof steps are discarded. |
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

For a positive existential target, the verifier checks an exact known
existential before specialized builtin existential routes. The successful
result therefore retains the existing source `FactId` for To-Lean replay;
later known-`forall` and builtin routes keep their existing relative behavior.

## Module and Bare-Name Resolution

Manifest imports and exports define a module namespace separate from the symbol
namespace. Therefore `A::x` always treats `A` as a module head, while bare `A`
is a symbol lookup; a module alias and local symbol may share the spelling.
Field access is separate again, so `.field` never enters module or bare-symbol
search.

By default, external symbols require their qualified names. The optional
`[allow bare export]`, `[allow bare import std]`, and `[allow bare import]`
tables select sources whose recursively public terminal symbols may be bare.
At source entry the runtime walks the current module and its ancestors, keeps
only already-loaded enabled targets, recursively visits their ordered public
exports (never private imports), and builds one unique `name -> canonical
owner, SymbolRef, role` index. Per-token lookup is then constant-time. Explicit
qualified names bypass it.

The same `SymbolRef` reached by re-export is harmless. Different symbols with
one terminal name are a configuration error, not an overwrite. An active entry
also reserves its spelling against source-created declarations and binders in
that file; compiler-generated binders and struct fields are outside that
reservation. Because an export contributes only after it is loaded, no earlier
file can resolve a later export through this mechanism. Isolated imports do not
populate the index.

## How Fact Shapes Run

Compound facts are not all handled in the same way. Their logical shape
determines which local assumptions or subgoals Litex creates.

The parser and AST deliberately maintain a canonical fact hierarchy:

- `AndFact` contains `Vec<AtomicFact>`: conjunction is flat and atomic-only.
- `OrFact` contains `Vec<AndChainAtomicFact>`: `or` is the outer grammar layer
  and receives already parsed atomic, chain, or flat-conjunction branches.
- `ForallFact::new(..., Vec<Fact>, ...)` is the surface-facing constructor. It
  may flatten a sole positive nested `forall` by merging parameters and
  premises. `new_canonical_forall(..., Vec<ExistOrAndChainAtomicFact>, ...)`
  accepts only the non-`forall` conclusion shapes used for storage.

Consequently, `$p(a) and $q(a) or $t(a)` has the two `or` branches
`($p(a) and $q(a))` and `$t(a)`. The `or` layer is above the `and` layer in the
grammar/AST; equivalently, `and` binds more tightly in operator-precedence
terminology. These types encode a fixed normal form, not arbitrary recursive
nesting of compound facts.

| Fact shape | Verification meaning | Context effect after success |
|---|---|---|
| Atomic fact, such as `x = y`, `x $in S`, or `$P(x)` | Check object well-definedness, then seek evidence through the atomic verification loop below. | Store the atomic fact and run its inference routines. |
| Chain, such as `0 <= x <= 1` | Expand the chain into its adjacent atomic relations and verify every step. | Make the component relations, and supported chain consequences, available. |
| Flat conjunction, such as `A and B` for atomic `A` and `B` | Verify every atomic component. Failure of one component fails the conjunction. | Store the component facts; each can be reused independently. |
| Outer disjunction, such as `A or B` where each branch is atomic, a chain, or a flat conjunction | Establish at least one branch, reuse an already known disjunction, or close the whole disjunction through a matching rule. | Store the disjunction. It does not make an unproved branch available. |
| `exist x S st {...}` | Establish existence through an explicit witness, a known existential, a known universal result, or a builtin mathematical route. | Store existence only. It does not bind `x` outside the fact. |
| `exist! x S st {...}` | Establish both existence and uniqueness. An explicit `witness exist!` must discharge the uniqueness obligation as well as the body. | Store unique existence and expose its routine uniqueness consequence. |
| `not exist x S st {...}` | Establish nonexistence as a fact, usually from known facts or an explicit proof route. | Store nonexistence and any representable routine logical consequence. |
| `forall x S: premises =>: conclusions` | In a child scope, bind arbitrary `x`, assume the premises, and verify every conclusion. A sole positive nested `forall` conclusion is first flattened by appending its parameters and premises. | Store a reusable flat universal rule. Local parameters and premises disappear, and no stored then-clause contains another `forall`. |
| `forall ... <=> ...` | Convert the equivalence into two universal directions, then check and verify each direction in an independent local scope containing the shared premises and that direction's antecedent. | Store both directions for later matching. |
| `not forall ...` | Establish the negation of the universal fact, often with an explicit contradiction proof. | Store the negated universal fact and any representable counterexample consequence. |

Well-definedness constructs quantified contexts incrementally. In a `forall`
premise list and an `exist`/`exist!` body, facts are checked in source
order inside the binder's child environment. Each successful check stores the
fact there and runs guarded inference before the next fact is checked. Thus a
positive concrete predicate can expose a definition clause such as a known
universal, and a later division or function body can consume the resulting
side condition. The inference reentrancy guard prevents recursive definition
cycles; abstract predicates have no clauses to expose; the child environment
is discarded after checking, so none of these temporary assumptions escape.

A `struct` `<=>:` block likewise checks its equivalent facts in source order
inside the temporary field scope, but stages each successful fact without
definition inference. Earlier filter guards can therefore justify the
well-definedness of later partial expressions. Declaration checking and later
instantiated-carrier checking use the same rule; reversing a required guard
still fails, and no staged fact escapes the struct check.

### The Atomic Verification Loop

Most proof obligations eventually ask for an atomic target. The public model is:

```text
atomic target
  -> all objects are well-defined
  -> zero-premise verification:
       -> match a known non-forall atomic fact, or
       -> directly evaluate the written atomic fact, or
       -> for equality, normalize an already known equality representative, or
       -> for equality, use terminating reductions and constructor congruence
          whose leaves need only known equality or direct evaluation, or
  -> try one premise-producing builtin mathematical rule, or
  -> run a strictly structural builtin strategy, or
  -> for equality at outer round 0, recursively compare matching object constructors, or
  -> verify a concrete definition at outer round 0, or
  -> match the conclusion of an applicable known forall and verify its premises, or
  -> run a user-defined strategy
  -> true or unknown
```

A premise is a child fact that a rule must verify before concluding its parent
fact. The builtin premise dispatcher accepts the quantifier-free AST layer:
atomic facts, flat conjunctions, relation chains, and outer disjunctions.
Conjunction and chains verify every atomic leaf; disjunction first reuses the
complete known fact and otherwise proves one selected branch. All leaves share
the incoming builtin-rule state, so compound syntax cannot reset the recursion
budget or enter the full verifier.

Zero-premise atomic verification generates no child facts and consumes no new
builtin-rule step. This is why a rule proving `x * 2 >= 0` from `x >= 0` may
still directly evaluate its closed premise `2 >= 0` after the multiplication
rule has consumed the allowed rule step. Equality uses the same boundary:
calculation and terminating constructor congruence run before a
premise-producing equality rule, while the fuller recursive equality route
remains outside zero-premise verification.

Closed `$prime(n)` and `$coprime(a,b)` goals use dedicated direct-evaluation leaves
after their natural-number domains are checked. Symbolic positive facts use
their explicit definitions: trial division for prime, and the non-all-zero
condition plus `gcd(a,b)=1` for coprime.

Ordinary non-equational computation stays on the atomic fact as written. It
does not unfold every argument through checked object definitions and retry on
a rewritten target. Equality-aware known-fact matching is a separate route and
requires an already proved source fact.

Within one statement, Litex reuses an exact successful atomic subgoal if that
same subgoal is requested again. This memo follows the ordinary environment
scope: a proof from a parent scope is valid inside a child, while a proof that
depends on child assumptions disappears when that child closes. It is cleared
at the end of the statement, including an `unknown` or error exit. A memo hit
reuses the original proof evidence only; it does not store the temporary fact,
rerun inference, or make the fact available to the next statement. The
statement's explicit commit and ordinary forward inference remain the only
ways its documented facts enter the continuing context.

### Goal-directed search and cache neutrality

Every automatic rule with a closed, finite premise family must derive its
candidate premises from the target fact family and the target object's
structure. It must not derive those semantic alternatives by scanning
whichever related facts happen to have been stored for the subject. For
example, to prove `e $in C`, standard-carrier widening checks the fixed proper
standard subcarriers of `C`; it does not enumerate the sets currently indexed
as containing `e`.

This gives three kernel-wide invariants:

- **Cache neutrality.** A cache hit may accelerate an existing proof route, but
  a cache miss is never evidence that a premise is unavailable. Every cached
  route must have an equivalent uncached, goal-directed route.
- **Closed-route materialization independence.** When a rule advertises a
  target-determined premise family, explicitly committing one of those
  already-derivable premises must not be required for the rule to find it.
- **Target-owned candidate generation.** Finite semantic alternatives are
  enumerated from the goal's closed rule table or constructor, never from a
  reverse index of facts previously observed about the subject.

Any change to a cache, reverse index, memo, or builtin dispatcher therefore
requires paired cold- and warm-context regressions with the same success or
failure result. Their evidence may differ only by a documented cache wrapper
that preserves the original proof certificate. This does not remove Litex's
deliberately bounded proof model: an explicit user lemma outside a rule's
advertised premise family may still enable a later proof.

**Builtin mathematical patterns.** The target shape is matched against
implemented arithmetic, equality, order, membership, set, function, and
composite-object rules.

Conceptually, builtin rules and builtin strategies mirror the two corresponding
user-facing proof mechanisms:

```text
builtin rule       <-> known forall fact
builtin strategy   <-> user-defined strategy
```

A builtin rule is the kernel-provided form of a universal fact application: it
matches one target and asks for the fixed premises of that mathematical step.
A representative arithmetic rule accepts `(a % m) % d = a % d` only after
checking `a in Z`, `m,d in N+`, and the computational divisibility premise
`m % d = 0`; an arbitrary pair of nested moduli is not absorbed.
A builtin strategy is the kernel-provided form of a user strategy: it
structurally transforms a target and may continue layer by layer while the
strategy shape still applies. They differ from their user-defined counterparts
mainly in where they are implemented, not in their proof role. This symmetry is
the design guide for recursion, failure, and proof-chain reporting; builtin
automation should not acquire symbol-specific control-flow exceptions.

A builtin rule has depth one: its premises are quantifier-free facts whose
atomic leaves use known non-`forall` facts or deterministic computation and
cannot invoke another rule. A known `or` premise is consumed as one complete
fact; it is never decomposed into an unjustified known branch. Builtin
strategies are a separate route for strictly smaller structural children; each
layer may try one fresh direct rule before repeating only that strategy.
Neither route enters the full verifier, known `forall` matching, definitions,
or user strategies, and the child result tree is returned to the root.

For example, the `not-equality symmetry` rule proves `b != a` from the exact
known child `a != b`. It records that reversed child in the proof tree and
returns unknown when no such non-equality fact is available.

Finite-endpoint nonemptiness first has a direct fast path for already-known or
computational order. Otherwise `closed_range(a, b)` and the closed real
interval `'[a, b]` reduce structurally to `a <= b`; half-open integer
`range(a, b)` and real intervals with an open endpoint reduce to `a < b`. The
endpoint-order fact is the smaller child and may use one fresh direct rule.
Missing order does not establish nonemptiness, and equal endpoints remain
empty whenever an end is open.

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
Generic reductions use the same bounded layer. Extensional operation checks
connect additive seed-zero and multiplicative seed-one folds to `sum`,
`product`, `finite_set_sum`, and `finite_set_product`. Reduction congruence
consumes `$fn_eq_in` on the visited range or finite set, finite-set reindexing
consumes an already-known `$bijective` fact, and disjoint-union reduction
consumes `intersect(A, B) = {}`. The generic union result nests one reduction
as the other's seed instead of assuming that an arbitrary seed is an identity.
Ordered adjacent-range composition is separate and remains valid for
noncommutative operations. A concrete prop may expose a matching operation
law as a known `forall`, but none of these routes invents an operation law,
pointwise equality, disjointness proof, or bijection.
For ordered `reduce`, an additional bounded rule recognizes translations
between equal-length closed integer ranges. It checks the pullback value at one
fresh target index, so `k` corresponds to `a + (k - c)` and the original value
order is unchanged. First- and last-step equations thread the accumulator
through the corresponding endpoint. Arbitrary bijections remain confined to
the associative-commutative `finite_set_reduce` route because a set bijection
does not preserve the ascending enumeration used by `reduce`.
Integer adjacency is another direct one-step rule: known integer objects and
`a < b + 1` prove `a <= b`, without recursively deriving an intermediate
shifted comparison.
Integer `range` and `closed_range` objects likewise expose a direct standard
carrier edge: they lie in `Z`, and a lower endpoint already in `N` or `N+`
proves the corresponding natural subset. The finite-set strategy treats a
set-builder as a filtered subset of its base, so finiteness recurses only to
that base.

Existential facts and set builders share a deliberately shallow property-body
grammar: atomic facts, flat conjunctions, chains, and disjunctions. They do not
store an anonymous `forall`. Quantified conditions are defined as named
concrete props and appear in these bodies as atomic `$P(args)` facts. This
keeps witness instantiation, alpha matching, set-builder membership, free-name
collection, and Lean lowering on one body representation.

The kernel-owned choice interface follows the same rule:
`$is_choice_function_for(I,S,g,f)` names
`forall alpha I: f(alpha) $in g(alpha)`. Therefore the canonical
`general_cart` set builder, the chooser produced by `by axiom_of_choice`, and
the upper-bound/maximal witnesses produced by `by zorn_lemma` all retain only
atomic facts in existential or builder bodies.

Definition-facing structural strategies are also bounded: dependent tuple
constructors are checked field by field; a one-field struct uses its sole
field carrier directly and projects that field by identity; callable fields
of multi-field structs project through one checked constructor; and
set-builder membership unfolds one literal, one
checked function/template definition, or one exact indexed named-builder
equality. The indexed route does not scan the environment for approximate
named definitions.

For known integers, the two singleton-interval rules retain both explicit
bounds: `n <= x < n + 1` gives `x = n`, and `n < x <= n + 1` gives
`x = n + 1`. Function extensionality can consume an exact cached pointwise
universal only when both declared function carriers are alpha-equivalent.
When a verified `$fn_eq(f, g)` is stored, atomic inference stores the ordinary
equality `f = g`. Later root and nested equality checks use the normal equality
class and constructor congruence; the equality verifier does not run a separate
`$fn_eq` lookup.

At outer round 0, equality never enumerates stored representatives or opens a
candidate graph. It may reduce one checked named-function application only
when that application is literally a side of the submitted goal, then compare
the result with the other goal side. Every comparison node first tries identity,
a stored non-forall equality class, pure numeric computation, bounded
obligation-free rational-expression normalization, capture-avoiding beta
reduction of one complete anonymous-function application layer, and
constructor descent. Remaining curried application layers are reapplied when
the substituted result is callable. It never opens the ordinary builtin
dispatcher, and beta-reduced comparison targets are not stored as facts.
Definition reduction does not instantiate known `forall`, follow equality
representatives to find another application, or recursively unfold a second
named definition. Function applications
align trailing argument groups and then compare their remaining function
prefixes, so the two sides need not have the same number of curried application
groups. Other atomic-fact lookup may use known-only congruence for transport,
but does not start the fuller child-proof route. If aliases hide a named
application on both sides, the program must state the bridge equality
explicitly. Thus `selected = f(a, 0) = f(1, 0)` exposes the direct congruence
step, while `selected = f(1, 0)` alone does not reopen the alias. A direct
ill-defined template use is still rejected by the ordinary well-definedness
check.
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
already known. The canonical spelling is `by def $P(args)`. The older
`by def:` plus `? $P(args)` block remains accepted for compatibility.
Supported builtin definitions use the same inline form, including
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
`by thm` provides an explicit theorem-instantiation route. The preview forms
`by thm name(args) => atomic_fact` and `by thm name(args):` followed by one
`? atomic_fact` perform that same instantiation in a child environment, verify
the requested atomic fact there, discard the child, and commit only the
requested fact to the parent. The requested fact must be well-defined before
the child is opened, so temporary theorem conclusions cannot be the sole
support for its object or callable shape.

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
| `let x = value` (preview) | The new object name becomes visible only after the right side passes. | `x` must be fresh; `value` must already be well-defined; the form accepts one name and one value. | No type or membership subgoal. | Bind `x`, store the ordinary equality `x = value`, then run existing equality inference. | Checked object definition with no declared carrier. |
| `have x S` | Introduces `x` in the current scope only after checks pass. | `x` must be unused; `S` must be well-defined. | Prove that `S` is nonempty. | Bind `x`, store `x $in S`, then infer. | Checked object introduction. |
| `have x S = value` | The defining value is checked before `x` is committed. | Name, type, and value must be well-defined. | Prove `value $in S` during `verify_process`. On failure, diagnostics name the required carrier, the narrowest provable standard numeric source carrier when available, and the uncommitted binding. | Bind `x`; store its type/membership and `x = value`; then infer. | Checked definition. |
| `have x S: body` | Uses an existential binder while checking the obligation. | The corresponding `exist x S st {body}` must be well-defined. | Prove that corresponding existential fact. | Bind an opaque witness `x`; store its type and instantiated body facts; then infer. | Checked existence, not unrestricted witness creation. |
| `obtain names from exist ...` or `obtain names from $P(args)` | Opens existential binders into the current scope. | Witness count, parameter types, and existential shape must match. The prop form retains a concrete definition and requires exactly one positive `exist`/`exist!` clause after argument substitution. | Verify the direct existential or the source prop fact; the executor rechecks the retained definition projection instead of trusting a parser rewrite. | Bind opaque witness names and store the instantiated direct body facts; positive concrete predicate bodies recursively expose their positive clauses under cycle guards. For positive `exist`, Litex-to-Lean retains a checked definition-projection certificate and then uses the ordinary `Exists.choose` path. | Adds no new trust. |
| `obtain names from thm name(args)` | The explicit theorem application lives in a disposable child scope. | The theorem must resolve, pass ordinary `by thm` argument/domain or builtin checks, expose all conclusions, and have exactly one direct positive `exist`/`exist!` conclusion with matching witness count. | Reuse `by thm`, identify its exact structured direct conclusion from theorem evidence, then run ordinary existential elimination. | Discard the theorem application's environment and intermediate existential; bind witnesses and store their types, direct body facts, inference, and uniqueness interface. The nested theorem result remains as provenance. Litex-to-Lean rejects the combined form until it has a theorem-application IR. | Adds no new trust; imported and builtin theorem trust/source boundaries are unchanged. |
| `prop P(params): clauses` | Parameters are local while the definition is checked. | Name, parameter domains, and clauses must be well-defined. | The clauses are not proved; they declare the meaning of `P`. | Store the concrete predicate definition. | A definition, not a theorem or assumption about existing objects. |
| `abstract_prop P(params)` | Parameters describe an interface only. | Name and parameter shape must be valid and nonconflicting. | None. There is no defining body. | Store the predicate symbol and arity. | Introduces no fact; later properties still need proof or explicit trust. |
| `struct Name: fields <=>: filters` | Header parameters, fields, and filter facts live in temporary definition scopes. | Field carriers are checked in declaration order. Equivalent facts are checked left to right and each successful fact is staged without inference for later well-definedness; instantiated carriers repeat the same check. | The filters are not proved; they define membership in the named product view. | Store the struct definition only after the complete check succeeds. | A checked definition, not an assumption that arbitrary field values satisfy its filters. |
| `have fn f(params) T = body` | Parameters and domain conditions are local. | Signature, domain conditions, return set, and body must be well-defined. Later domains may cite earlier parameters; the return set may cite all function parameters and is instantiated with actual arguments at application. | Prove `body $in T` under the parameter and domain assumptions; an annotation never supplies this fact by itself. | Store `f`, its function type, defining equation, and callable body facts. | Checked mathematical definition. |
| `have fn f(...) T by cases` | Each case is checked under its own local condition. | Signature, cases, conditions, and return expressions must be well-defined. | Prove coverage, mutual exclusivity, and return membership for every case. | Store the function and the case-specific universal equations. | Checked mathematical definition. |
| `have fn f(...) T by induc ...` | Base and recursive cases receive induction-local bindings. | Signature, measure, lower bound, cases, and recursive calls must have valid shapes. | Check the lower bound, coverage, return membership, and strict decrease of recursive calls. Later uses may select a provable case and normalize arithmetic inside its instantiated equation. | Store the recursive function definition and its usable equations. | Checked definition with termination obligations; an unproved case condition never authorizes unfolding. |
| `have fn f by exist!` | Its proof, when supplied, runs in a child scope; template materialization substitutes through local `obtain`, `witness`, equal-object and function definitions, case, and extension statements. | The source must have the expected parameterized unique-existence shape. Refined function-space return carriers remain callable after materialization. | Verify the source `forall ... exist! ...` fact or its proof block. | Store the selected function, its type, defining property, uniqueness fact, and materialized local proof consequences. | Checked use of unique existence. |
| `have algo for f(params)` | Implementation parameters and cases are local. | `f` must already be a function; parameters must match its mathematical signature. | Check each executable result and case against the established function facts. | Attach executable data used by `eval`; do not replace the mathematical definition. | Adds no mathematical assumption. |
| `eval expression` | None. | The expression must be supported and evaluable. | Compute the supported value; there is no separate proof of the resulting equality. | Report and store `expression = value`. | No user trust; the evaluator is part of the implementation's trusted surface. |

Callable lookup is direct-first. If an application head has no directly
registered function signature, the runtime may inspect its already stored
equality class and reuse a representative's checked signature and one-step
definition. It then performs the same arity, domain, and side-condition checks
as a direct call. This well-definedness fallback reads existing indexes only;
it does not enter general equality, builtin, definition, or `forall` proof
search.

### Proofs, Theorems, and Trust

| Form | Local scope | Structural / well-definedness checks | Verification / subgoals | Commit on success | Trust boundary |
|---|---|---|---|---|---|
| `claim: ? target ...` | Proof steps run in a child scope; a universal target also opens parameters and premises there. | The target must be well-defined. `claim` does not accept a universal equivalence target. | Execute the proof, then verify the target or all universal conclusions. | Store the target and infer in the parent scope. | Checked; any explicit trusted step remains visible as its own statement result. |
| `example: ? target ...` | Proof steps run in a child scope; a universal target also opens parameters and premises there. | The target must be well-defined. `example` does not accept a universal equivalence target. | Execute the proof, then verify the target or all universal conclusions. | Nothing. The outer context is unchanged. | Checked; any explicit trusted step remains visible in the result but is not exported. |
| `thm name: ? forall ...` | Theorem parameters and premises live in a child proof scope. | The name must be unused and the universal statement well-defined. | Execute the proof and verify every conclusion. | Store the named theorem and its universal fact. | The theorem itself carries no transitive trust tag; direct trusted proof steps remain separately countable. |
| `axiom name: ? forall ...` | No proof scope is needed. | The named universal statement must be well-defined. | No truth proof. | Store a named theorem-like interface and universal fact. | Explicit axiom; rejected in strict mode. |
| `trust facts` | The statement stages all facts in a temporary child environment; later facts can use earlier staged facts. | In user code, every assumed fact must still be well-defined and storable. | No truth proof. | Atomically merge all unsafe assumptions and inferred consequences only after every fact succeeds; discard the child on failure. | Explicit proof debt; rejected in strict mode. |
| `trust have ...` | The new bindings, their facts, and inference run in one temporary child environment. | Bindings, types, and attached facts must be valid enough to store. | No truth proof of the attached facts. | Atomically merge the names, type facts, attached assumptions, and inferred consequences; discard all of them on failure. | Explicit proof debt; rejected in strict mode. |
| `sketch: ...` | All nested statements run in a child scope. | Each nested statement performs its normal checks. | Nested proof obligations run normally. | Nothing. The outer context is unchanged. | Any nested trust remains visible in the result but is not exported. |
| `try: ...` | All nested statements run in a child scope. | Each statement performs normal checks; controls that cannot be merged are rejected. | Every step must succeed; `unknown` aborts the block. | Commit the complete child environment atomically. | Inherits any trust used by committed nested statements. |
| `witness exist ... from values` | Existential parameters are locally equated with the proposed values. | Witness count, values, types, and existential body must be well-defined. | Check witness types and every instantiated body fact; `exist!` also checks uniqueness. | Store the existential fact and infer. Witness parameter names do not escape. | Checked witness proof. |
| `witness $P(args) from values` | The proof runs without exposing the existential binder names; the AST retains the named positive prop rather than expanding it. | At execution time the active concrete prop must have exactly one positive ordinary `exist` clause; arguments, witness count, values, types, and instantiated body must be well-defined. `exist!`, `not exist`, abstract, nonexistential, and multi-clause definitions are rejected. | Freeze the concrete definition and instantiated existential, then reuse the ordinary existential witness checks. Unique existence stays on explicit `witness exist! ...`, followed by `by def` when a named prop is required. | Store `$P(args)` as the primary fact; normal definition inference exposes the exact `exist` consequence. Litex-to-Lean folds it with checked `DefinitionIntroduction` evidence. | Checked witness proof; neither parser nor compiler performs a definition rewrite or fresh lookup. |
| `witness $is_nonempty_set(S) from value` | The proposed value is checked locally. | `S` and `value` must be well-defined. | Prove `value $in S`, or the corresponding supported function-set condition. | Store nonemptiness and infer. | Checked witness proof. |

### Explicit Proof Routes

Each route below generates or checks subgoals. Those subgoals return to the
same fact and atomic verification loops; a proof route is not a second,
unrelated verifier.

In every `by ...:` goal-block route, the ordinary user proof list may be empty;
the route still has to close its goals with its normal final verifier. Case arms
and induction branch headers remain structural inputs. `by contra` alone must
retain an explicit final `impossible` statement.

| Form | Local scope | Structural / well-definedness checks | Verification / subgoals | Commit on success | Trust boundary |
|---|---|---|---|---|---|
| `by def fact` | No persistent child scope. | The single target must be a concrete positive prop or supported positive builtin definition. The older goal-block spelling remains parser-compatible. | Verify every defining requirement with the full verifier, even if the target is already known. | Store the target and infer only after all requirements succeed. | Checked use of a definition. |
| `by thm name(args)` | The instantiation is checked against the current scope. | A user theorem must exist and match its arguments; a reserved builtin theorem checks fixed arity and requirements. The reduced-fraction theorem requires `q $in Q`; finite-subset closure requires an explicit subset premise and finite superset; finite-set indexing requires a finite set. | Verify theorem domains or explicit builtin requirements with the full verifier. `rational_has_unique_reduced_fraction(q)` constructs its fixed existential and checks its well-definedness instead of relying on an implicit existential rule; `finite_set_has_bijective_index(s)` constructs a noncanonical `idx : finite_seq(s, finite_set_size(s))` bijective from `closed_range(1, finite_set_size(s))`. | Store conclusions and infer only after all checks succeed. The finite-subset theorem is explicit and does not turn subset chains into automatic search; arbitrary finite sequences are not inferred bijective. | Builtin names remain bare and globally reserved; detailed output identifies `builtin_rule` source and any provenance. |
| `by thm name(args) => atomic_fact`, or `by thm name(args):` plus one `? atomic_fact` goal (preview) | The ordinary theorem application and its inferred consequences live in a disposable child scope. | The selected atomic fact must be well-defined in the parent; theorem lookup, arguments, domains, and builtin shapes use the legacy checks. The goal-block spelling accepts no proof body. | Apply the theorem in the child, then use the full atomic verifier on the selected fact. | Discard the child and transactionally store only the selected fact as the parent seed; ordinary inference from that seed remains enabled. | Detailed output separates `temporary_then_facts`, `target_check`, and `parent_stored_facts`; strict/trusted execution follows the existing theorem and file trust boundaries. |
| `by cases` | One child scope per case. | Target, cases, and branch shapes must be well-defined. `case fact` denotes a zero-statement proof branch; branches with statements use `case fact:`. | Prove the cases are exhaustive, then prove every target in every branch, including after zero proof steps in a bodyless branch. | Store the common target facts and infer. | Checked case analysis. |
| `by contra` | A child scope assumes the logical negation of the target. | The target must support logical negation and be well-defined. | Execute the proof and verify both a stated impossible fact and its negation. | Store the original target and infer. | Checked contradiction proof. |
| `by induc` / `by strong_induc` | Separate base and step scopes with ordinary or strong induction hypotheses. | Parameter, starting point, target, and induction shape must be valid. | Verify base and step obligations. | Store the resulting universal fact and infer. | Checked induction. |
| `by induc P:` (finite-set induction) | Separate empty/base and insertion-step scopes. | The finite-set parameter and goal shape must be valid. | Verify the base and element-adjoining step. | Store the resulting universal fact and infer. | Checked induction. |
| `by extension A = B` or its goal-block form | Element arguments and subset directions are checked in local scopes. | Both sides must be well-defined sets of the supported shape. Inline syntax is accepted only with no indented proof body. | Prove both inclusion directions. | Store set equality and infer. | Checked extensionality proof. |
| `by enumerate finite_set:` with an indented `? forall ...` goal | One child assignment for each displayed element. | The finite set and universal target must have the expected finite shape. | Verify the target for every assignment. | Store the universal fact and infer. | Checked finite proof. |
| `by enumerate range` / `by closed_range as cases` | No proof facts escape beyond the generated result. | Membership and integer endpoints must be well-defined. | Verify the membership prerequisites and expose the corresponding equality cases. | Store the generated equality or disjunction. | Checked range expansion. |
| `by for:` with an indented `? forall ...` goal | One child assignment per supported finite iteration value. | Iteration domain and universal target must be well-defined and finite in the supported form. | Verify the target for every assignment. | Store the universal fact and infer. | Checked finite iteration. |

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
| `unknown` | The verifier found the target meaningful but could not establish it from the visible context and supported routes. This does not mean false. A bare top-level fact surfaces this as a verification failure whose reason is `unknown`, not as a successful statement. Nested function-application equality failures may additionally report the unmatched application, nearest known prefix equality, and remaining argument count. | The target is not committed as a proved fact. Add a missing premise, equality, witness, case, or intermediate result; prefix guidance is diagnostic only and does not add congruence. |
| `error` | Parsing, name resolution, statement shape, scope, or well-definedness failed, or a proof block violated its execution contract. | The failed target is not committed as a verified result. Supporting effects may already be present unless the form explicitly documents a discarded child or atomic commit. In particular, failed `trust`, `trust have`, and `try` statements do not expose their child-environment effects. |
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

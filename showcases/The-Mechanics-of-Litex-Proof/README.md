# The Mechanics of Litex Proof

This is the registered Litex teaching module, with
citation theorems, Chapters 0–10 and the final lesson-status export. The ordered
public module entry is [`litex.config`](litex.config).

Build and run the whole book from the repository root:

```sh
cargo build --release
target/release/litex -strict -r showcases/The-Mechanics-of-Litex-Proof
target/release/litex -r showcases/The-Mechanics-of-Litex-Proof
```

For a configured chapter checkpoint, use `-strict -f` with its path. Current
CLI output must report `run_result: "success"`, `session_terminated: false`, `termination: null` and exit code 0.
The repo JSON summarizes success; it does not expose per-export statement
counts. The complete configuration contains 14 exports; no active trust, axiom or
abstract proposition remains.
The public source and manifest are the maintained release artifact.

When the book introduces a concept already supplied by Litex, it first explains
the mathematical definition and checks small examples, then comments the switch
to builtin objects. Later division/remainder/gcd work uses `quot`, `%` and `gcd`.
The native quotient lesson uses positive divisors; native gcd excludes `(0,0)`.
Negative divisors use a signed quotient with a nonnegative remainder. The former
total algorithms are preserved as historical source text in the workspace and
are not asserted equivalent at those domain/value boundaries. Pascal retains
its original recursion; Bezout uses an ordinary proved citation theorem.
The natural-set shift example in Chapter9 has its predicate signature corrected
to `power_set(N)`, matching its function, prose and witnesses.

## Proof boundary used by the book

Atomic proof search follows a visible order:

1. an already-known non-forall atomic fact;
2. deterministic builtin computation or one direct builtin rule;
3. a structural builtin strategy;
4. an applicable known forall visible in the current runtime;
5. a user-defined strategy.

A direct builtin rule does not recursively call another direct rule. A builtin
rule premise may use a known non-forall fact or deterministic computation. A
builtin strategy may descend through a strictly smaller constructor shape;
each immediate child is checked first as a known fact or computation and then
with one fresh direct rule before further structural decomposition.

The corresponding source interfaces are:

- `by def` introduces a positive defined predicate after its mathematical body
  has been proved. Negative predicates continue to use ordinary proofs such as
  `by contra`.
- When a concrete predicate's whole body is one positive ordinary `exist` fact,
  `obtain k from $p(args)` and `witness $p(args) from value` cross that named
  boundary directly at runtime. Named construction excludes `exist!`, which
  uses explicit `witness exist! ...` plus `by def`. Raw existentials, abstract
  predicates, nested local definitions, and multi-clause definitions also keep
  their explicit forms.
- `release thm <builtin-name>(...)` invokes a named semantic object rule, such as
  `set_builder_member` or `tuple_equal_from_coordinates`. These interfaces are
  not silently included in automatic atomic search.
- A nested function application is unfolded one function definition at a time.
  The carrier of an immediate compound argument is stated before evaluation
  when the domain check needs it as a known leaf.
- Automatic known-forall instantiation uses the candidates visible in the
  current runtime, which may include earlier exports or referenced imported
  modules. Use qualified `release thm` when the dependency should be explicit or
  automatic matching does not supply the intended instance; a local claim may
  deliberately turn that result into a nearby reusable forall.
- `let name = value` is used for a proof-local equality alias when the value's
  carrier need not be established separately. Keep typed `have` when its
  carrier fact is part of the proof, especially for products, sets, and
  iterated objects.
- A witness may omit its indented body when the substituted existential body is
  already known. Chapter 8 exposes `inverse_implies_bijective` and
  `bijective_implies_has_inverse`; examples that check both inverse equations
  reuse the first theorem instead of reopening injectivity and surjectivity.
- Arithmetic source makes the prefix-minus/power boundary explicit: use
  `-(t^2)` or `-1 * (t^2)`, `(-t)^2`, and `t^(-1)`. Although the parser reads
  bare `-t^2` as `-(t^2)`, the book does not use that implicit spelling.

The mathematical rationale and dependency map live in
[`math_collections.md`](math_collections.md). Working journals are intentionally
kept outside the published module.

## Editing workflow

For proof-authoring workflow, use the repository [Agent Guide](../../docs/AgentGuide.md).
Finish a changed file with a clean configured `-strict -f` gate. Whole-book
verification uses the actual `-r` entry above, never an inference from isolated
chapter results. Preserve source statements, domains and teaching comments.

## Callable coordinates and recurring mathematical values

Finite tuples use ordinary function application: `p(1)`, `p(2)`. Their complete
carrier is checked with Cartesian or `finite_seq` membership; retired indexing
and `tuple_dim` are not part of the book's current interface.

The number-theory product uses the named identity `factorial_factor` on `N+`.
The real-function lessons name `real_successor` and `real_square`, and the set
lesson names the two sets of multiples. These definitions retain the original
mathematics while letting later statements cite the same mathematical values.

The relation lesson defines `\equivalence_class<X, a>` as
`{b X: $rel(a, b)}`. The template retains the representative's carrier and
lets the symmetry/transitivity proof reuse one class value on each side.

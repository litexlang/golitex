# Newton iteration: a residual estimate

This compiler experiment, selected on 2026-10-13, targets the residual estimate
for every natural index. The single-step identity and the positive-real update
have completed compilation and native consumption. The compiler now also
consumes bounded absolute-value, natural-power, recursive-function and
zero-based induction results. Acceptance of the complete bound and its native
consumer is still pending.

## The mathematical target

Let

\[
x_0=1,\qquad x_{n+1}=\frac{x_n+2/x_n}{2},\qquad
g_n=|x_n^2-2|.
\]

Prove, for every natural number \(n\),

\[
g_n\le 4(1/4)^{2^n}.
\]

Here `gap` means the residual of the equation `x² = 2`. It does not mean
`|x - sqrt(2)|`. A distance estimate, convergence theorem, floating-point
roundoff analysis and executable extraction are outside this experiment.

The proof has five dependent steps:

1. Show that the positive-real update is legal and prove
   `4*x^2*residual(newton(x)) = residual(x)^2`.
2. Show that the next residual is nonnegative. Convert the identity into the
   corresponding identity for absolute residuals.
3. Prove `newton(x) > 1` for positive `x`, then use induction to prove
   `x_n >= 1`, including equality at `n = 0`.
4. Substitute the iterate into the gap identity and use `x_n^2 >= 1` to get
   `g_(n+1) <= g_n^2 / 4`.
5. Prove that `B_n = 4*(1/4)^(2^n)` has initial value one and satisfies
   `B_(n+1) = B_n^2/4`. Induction and monotonicity of squaring on nonnegative
   reals give `g_n <= B_n`.

The final numerical checkpoint is `g_2 <= 1/64`; its actual value is `1/144`.
The estimate is correct but deliberately not sharp.

The standalone [full proof source](../../../../lean/examples/newton_residual_bound/statement.lit)
contains this argument, drawn from the existing
[numerical-analysis showcase](../../../../showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit).
Its core declarations are the following excerpt, which requires the preceding
definitions and proofs in that file:

<!-- litex:skip-test -->
```litex
have fn newton_sqrt_two(x R+) R+ = (x + 2 / x) / 2

have fn sqrt_two_newton_iterate(n N) R+ by induc n from 0:
    case n = 0: 1
    case n > 0: newton_sqrt_two(sqrt_two_newton_iterate(n - 1))

have fn sqrt_two_newton_gap(n N) R = |square_root_two_residual(sqrt_two_newton_iterate(n))|
have fn sqrt_two_newton_gap_bound(n N) R+ = 4 * (1 / 4)^(2^n)
```

The complete source passed the current release CLI's strict verification on
2026-10-13. It contains no user `trust`, `axiom` or `abstract_prop`. The separate
[ordinary Lean proof](../../../../showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/same_math_in_lean.lean)
also passed Lean 4.31.0 with the pinned Mathlib revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. That file is a handwritten baseline,
not compiler output. These checks do not establish a comparative authoring or
runtime advantage.

## The completed single-step compiler slice

The independent [source](../../../../lean/examples/newton_residual_identity/statement.lit)
is:

```litex
# Newton's exact algebraic error identity for a nonzero real input.
have fn newton(x R:x!=0) R=(x+2/x)/2
forall x R:
    x!=0
    =>:
        newton(x)^2-2=((x-2/x)/2)^2
```

Its paired [Lean file](../../../../lean/examples/newton_residual_identity/statement.lean)
is actual CLI output. The function object is `_object_i1`, its function-space
membership is `h_357`, and the universal identity is `h_361`. The generated
input remains a generic `Litex.Obj` with representation evidence, membership
`h_374` and nonzero fact `h_359`. Each call carries the original function,
membership and guard certificates.

[Adapter.lean](Adapter.lean) explicitly instantiates the reviewed numeric model
and observes the generated equality as a real equality. Its proof consumes
`h_361`, the function-graph evaluation law, operation denotation laws and native
injectivity; it does not repeat the algebraic proof with `ring` or `field_simp`.
[Final.lean](Final.lean) is the ordinary Lean consumer:

```lean
theorem newtonResidualIdentity (x : ℝ) (hx : x ≠ 0) :
    ((x + 2 / x) / 2)^2 - 2 = ((x - 2 / x) / 2)^2 := by
  exact Adapter.newtonResidualIdentity x hx
```

This is a supporting lemma for the complete experiment. It is not a compiler
proof of the recursive residual estimate. The native theorem has no Litex
concepts in its statement; its proof dependency must reach the generated
identity through Adapter. Pinned Lake checks, a dead-binding control and the
standard-axiom audit are required for this slice.

## Completed stage 1: the positive-real update

The [positive-update source](../../../../lean/examples/newton_positive_update/statement.lit)
is a standalone proof, followed by the function whose return constraint that
proof establishes:

```litex
# Newton's update preserves positive real inputs and makes every division legal.
claim:
    ? forall x R+:
        (x + 2 / x) / 2 $in R+
    x > 0
    x != 0
    2 / x > 0
    x + 2 / x > 0
    (x + 2 / x) / 2 > 0

have fn newton_sqrt_two(x R+) R+ = (x + 2 / x) / 2

forall x R+:
    newton_sqrt_two(x) $in R+

newton_sqrt_two(1) $in R+
newton_sqrt_two(1) = 3 / 2
```

Its [generated Lean](../../../../lean/examples/newton_positive_update/statement.lean)
contains the claim `h_2`, function object `_object_i2`, function-space member
`h_5603` and universal return-membership theorem `h_5606`. These names come from
the original source identities. The claim consumer dispatches the actual
forall/non-forall body result and replays its parameter introductions, domain
assumptions, body statements, conclusion proofs and stores. The producer now
retains those already computed stages; execution and proof search are unchanged.

`R+` is the separation of `R` by positive-real membership in the existing set
semantics. A source parameter still has a generic host representation and an
ordinary `In a RPos` fact. Function inputs use a real carrier plus the proved
positive guard; function returns refer to the actual positive-real set.

The selected `PosAddPosIsPos` and `QuotientPositiveSameSignPos` evidence is
consumed by `Litex.addPositive` and `Litex.divPositive`. Every division keeps
the exact original operand-membership and nonzero certificates. The generated
return proof therefore establishes membership in `RPos`, rather than just `R`.

[PositiveAdapter.lean](PositiveAdapter.lean) observes `h_5606` through the
explicit numeric model, graph evaluation and denotation bridges.
[PositiveFinal.lean](PositiveFinal.lean) exposes the ordinary Lean theorem:

```lean
theorem newtonPositive (x : ℝ) (hx : 0 < x) :
    0 < (x + 2 / x) / 2 := by
  exact Adapter.newtonPositive x hx
```

The native proof dependency reaches `h_5606` and the function's return proof
reaches `h_2`. The handwritten adapter does not supply an independent proof of
the update's positivity. Both this pair and the residual-identity pair passed
strict source verification, actual compilation, byte-for-byte regeneration,
pinned Lean checks and the standard-only axiom audit.

## Implemented replay scope

Absolute value keeps its own `Litex.AbsObj`, original argument WD and real
membership proof. Its observations and selected nonnegativity, nonnegative
identity and even-power rules use proved denotation bridges. Symbolic natural
powers observe the original N-member as a native natural number without
changing its host representation; product-of-powers and power-of-power rules
consume their ordered base and exponent certificates. Selected order rules
retain the original sum, product, difference or quotient, including its
division guard and the exact zero endpoint when present.

The recursive slice accepts one N parameter, that parameter as the measure,
literal lower bound zero, no authored domain clauses, and the two ordered leaf
cases `n = 0` and `n > 0`. The base body has no self call; successor self calls
use the source argument `n - 1`. The compiler constructs an owned
`Litex.RecursiveNatFn` graph, whose internal interpretation uses `Nat.rec`.
Its result retains the binder, restricted self-membership, case stores,
selected guard path, original call WD and residual equality. Natural-index
coverage `n = 0 or n > 0` is replayed from its checked disjunction evidence.

Ordinary `by induc k from 0` supports nonempty atomic or flat And/chain goals
with supported constructors and proof routes. The original checked integer
parameter and zero lower-domain proof lead to separate base and step scopes.
Each scope replays its own assumptions, induction hypothesis, statements and
conclusion proofs; only the final stored forall is exported. Strong induction,
other lower bounds, general recursion measures and nested recursive cases
remain separate unsupported routes.

Theorem release retains the already computed type stores, domain stores,
local conclusion WD and caller WD/store pairs in execution order. Known-forall
equalities consume their original citation, argument-match tree and ordered
requirements, including an explicitly captured reversed equality for symmetry.
Claim and induction helpers stay inside their source scopes. Missing, changed
or future evidence is rejected by its original ID and subject; the compiler
does not search for replacement evidence in the final environment.

## Current evidence and remaining gates

The compiler regression suite passed 407 tests. Subsequent focused checks
passed six known-forall equality tests and three function-expansion Abs tests,
including evidence-corruption controls. Smaller generated recursive graphs,
recurrence steps, zero-based induction and arithmetic fixtures passed ordinary
pinned Lean checks. The four quotient-versus-zero orientations and direct and
symmetric known-forall equalities were checked from their actual generated
files. The generated prefix through the scaled residual identity also passed
its recorded resource-bounded Lean check. These results establish the reviewed
routes and that prefix, not the complete Newton estimate.

The standalone full source has passed strict verification. Whole-file
generation, ordinary Lean checking of the complete generated proof, and a
native all-index Adapter/Final with live dependence on the generated bound
remain pending, together with final regeneration and standard-only axiom
audits. A partial prefix or a resource-bounded check does not close those gates.
No complete generated bound or native bound consumer is presented here as an
accepted artifact.

## Implementation stages and acceptance

1. **Positive-real functions and proof blocks — completed.** Replay successful `claim`
   evidence and preserve `R+` as the derived positive-real set. Both the input
   domain and return constraint must survive compilation. Do not compile an
   `R+` return declaration as an unrestricted `R` return.
2. **Single-step residual calculation — bounded consumers implemented.** Owned
   absolute value, observations and selected equality/order rules are present.
   The complete scaled gap identity remains part of whole-file acceptance.
3. **Natural indices and powers — bounded consumers implemented.** Native
   natural observation preserves the original N-member; selected power laws
   preserve their ordered certificates. The bound recurrence remains part of
   whole-file acceptance.
4. **Recursive function objects — bounded consumers implemented.** Unary
   natural recurrence from zero retains the source graph, case selection and
   original recursive-call WD/return evidence. Smaller graph and recurrence
   checks passed; general measures and nested recursion remain outside scope.
5. **Inductive proof replay — bounded consumer implemented.** Original base
   and step scopes are replayed through the proved zero-based integer/natural
   bridge. Both complete Newton inductions and their final bound still require
   the whole-file and native gates.
6. **Complete native consumption — pending.** Generate the whole Litex file and export
   the residual estimate through Adapter to a theorem about an ordinary
   `ℕ → ℝ` sequence. Require a live dependency on the generated bound, not an
   independent Mathlib induction in Adapter.

Each stage requires the unchanged mathematical conclusion, exact typed-result
replay, source and compiler gates, byte-for-byte regeneration, real Lean checks,
standard-only axiom dependencies and an executable nearest rejected boundary.
Gate scripts, detailed results and receipts remain local in
`scripts/litex_to_lean/`; they are not part of the public Lean library.

The approved function-target interface is implemented in `Litex.lean`:

```lean
structure FunctionSignature (M : Semantics) where
  inputs : NumericInputDomain
  output : M.Value
  output_isSet : M.isSet output
  guard : M.Value → Prop
```

`FunctionSignature.oneTarget`/`twoTarget`, `formulaFnTarget`/`formulaFn2Target`
and `callTarget`/`call2Target` accept the actual set and its sethood certificate.
Their output-membership and beta laws are proved from the existing graph laws.
The existing numeric constructor and call spellings still supply standard sets
with proved sethood. This adds no semantic axiom or parallel call-object model.
The compiler currently accepts the five standard numeric targets and `R+`;
the broader Core interface alone does not promise arbitrary-set compilation.

Run source verification and compiler generation separately with the current
release build:

```bash
cargo build --release
target/release/litex -strict -lang en -f showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit
target/release/litex -strict -lang en -f lean/examples/newton_residual_bound/statement.lit
target/release/litex -strict -lean -f lean/examples/newton_residual_bound/statement.lit
target/release/litex -strict -lean -f lean/examples/newton_residual_identity/statement.lit
target/release/litex -strict -lean -f lean/examples/newton_positive_update/statement.lit
```

The strict commands verify the showcase and standalone full proof source.
The full-proof generation command is a pending acceptance gate, not a receipt
of a checked all-index Lean theorem. The final two commands generate the
maintained supporting pairs.

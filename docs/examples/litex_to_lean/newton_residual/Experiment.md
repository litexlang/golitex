# Newton iteration: a residual estimate

This is the next compiler experiment, selected on 2026-10-13. Its mathematical
target is the complete residual estimate, rather than a fixed number of
evaluations. Only the single-step identity has completed compilation and native
consumption so far. The recursive proof remains an explicit implementation goal.

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

The existing complete [Litex source](../../../../showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit)
contains this proof. Its core declarations are the following excerpt, which
requires the preceding definitions and proofs in that file:

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
not compiler output. The current source has 284 lines and that baseline has 146;
neither line count establishes an authoring advantage.

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

## Current rejected boundaries

The full source's first compiler rejection is statement 2, `ProofBlock`.
Removing the extraction-only `algo` does not remove that rejection. A reusable
named positivity theorem verifies in Litex but is rejected at
`StandardSet/SignedOrNonzero`; replacing `claim` alone is insufficient.

Independent strict-source probes also establish these boundaries:

| Source | Current compiler rejection |
| --- | --- |
| `by induc k from 0: ? k = k` with body `k = k` | `By` |
| `forall x R: |x| >= 0` | `WD/ArithmeticOperator` |
| `forall n N: 2^n $in N` | `WD/Pow/NonClosedIntegerExponent` |

Each probe passed strict source verification and failed compilation with exit
one and empty stdout. Separately, the current dispatcher explicitly rejects
`HaveFnByInduc` and its definition-unfold route. The full source's earliest
error does not establish that these are its only missing routes.

There is also a producer evidence gap in recursive unfolding:

```rust
pub struct ByUnfoldHaveFnByInducApplicationObjectDefinitionProof {
    pub expanded_body: Obj,
    pub residual_equal: VerifyFactResult,
}
```

The producer already verifies the chosen case guards, but its matcher returns
only the expanded object. Replay needs the successful root-to-leaf case path
and the actual guard results retained by that producer. It must not rediscover
a branch from the target equality. This is a localized result-capture candidate;
it does not authorize changing AST shapes, Runtime state or proof search.

## Implementation stages and acceptance

1. **Positive-real functions and proof blocks.** Replay successful `claim`
   evidence and preserve `R+` as the derived positive-real set. Both the input
   domain and return constraint must survive compilation. Do not compile an
   `R+` return declaration as an unrestricted `R` return.
2. **Single-step residual calculation.** Add an owned absolute-value object,
   its WD/observation laws and the actual selected equality/order rule adapters.
   Compile the exact scaled gap identity and the positive-input lower bound.
3. **Natural indices and powers.** Derive a proof-independent native natural
   observation from `In n N`, preserving the source host representation. Reuse
   Core's existing natural-power constructor with that observed index; replay
   the selected power laws and their certificates. Compile the bound recurrence.
4. **Recursive function objects.** Initially support the actual unary natural
   recurrence from zero, while retaining the Litex function graph. A native
   `Nat.rec` is its internal interpretation, not a replacement source function.
   Retain case-selection evidence and the original recursive-call WD/return
   proofs. General integer measures and nested recursion remain rejected until
   separately supported.
5. **Inductive proof replay.** Compile the base and successor proof results,
   their exact assumptions and the induction hypothesis. The producer's
   `by induc` conclusion is over integers above its lower bound; restrict the
   initial bridge to the checked zero-based case and prove the integer/natural
   correspondence. Compile both actual inductions and the final residual bound.
6. **Complete native consumption.** Generate the whole Litex file and export
   the residual estimate through Adapter to a theorem about an ordinary
   `ℕ → ℝ` sequence. Require a live dependency on the generated bound, not an
   independent Mathlib induction in Adapter.

Each stage requires the unchanged mathematical conclusion, exact typed-result
replay, source and compiler gates, byte-for-byte regeneration, real Lean checks,
standard-only axiom dependencies and an executable nearest rejected boundary.
Gate scripts, detailed results and receipts remain local in
`scripts/litex_to_lean/`; they are not part of the public Lean library.

The first semantic interface to settle is the function target. Currently:

```lean
structure FunctionSignature (M : Semantics) where
  inputs : NumericInputDomain
  output : StandardSetValue
  guard : M.Value → Prop
```

`StandardSetValue` only contains `N`, `Z`, `Q`, `R` and `C`. A proposed
generalization is to use the existing set-graph semantics directly:

```lean
-- Design proposal only; not an implemented Core declaration.
structure FunctionSignature (M : Semantics) where
  inputs : NumericInputDomain
  output : M.Value
  output_isSet : M.isSet output
  guard : M.Value → Prop
```

Then `R+` can be the proved separation of `R` by positivity, and the old
numeric constructors can keep their public spellings by supplying standard
sets. This adds no semantic axiom, but changes the Core target interface,
formula return proofs and call-output consumers. An alternative is a narrower
numeric-target representation:

```lean
-- Alternative proposal only; not an implemented Core declaration.
inductive NumericTarget (M : Semantics) where
  | standard (set : StandardSetValue)
  | restricted (base : StandardSetValue) (guard : M.Value → Prop)
```

Its restricted target would use the existing separation laws. It supports
this experiment but postpones arbitrary-set codomains. Neither change
has been implemented in this baseline. The choice must be settled before the
first stage changes the shared function interface.

Reproduce the source and compiler boundaries with the current release build:

```bash
cargo build --release
target/release/litex -strict -lang en -f showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit
target/release/litex -strict -lean -f showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit
target/release/litex -strict -lean -f lean/examples/newton_residual_identity/statement.lit
```

The second command verifies the full source; the third currently rejects it.
Only the fourth generates the maintained single-step pair.

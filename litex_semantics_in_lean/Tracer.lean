import Core

/-!
# Tracer: `a > 0`, `b > 0` implies `a + b > 0`

This is the smallest complete builtin-rule replay. The theorem statement is
still Litex-facing. Only the proof body crosses the native bridge, invokes
Mathlib's `add_pos`, and wraps the result back into the Litex `Gt` relation.
-/

namespace LitexSemanticsInLean

namespace Tracer

open Core
open API

/- The Rust verifier would serialize this information as a stable rule id and
ordered FactId citations. The Lean theorem receives the corresponding fields
as ordered arguments, so it never searches for a different proof route. -/
inductive RuleId where
  | realAddGtZero
deriving Repr, DecidableEq

structure Evidence (rule : RuleId) where
  sourceRule : String
  childFactIds : List String

/-!
The Litex source shape is:

```text
a $in R, b $in R, a > 0, b > 0 => a + b > 0
```

The four hypotheses remain `In` and `Gt`. `ℝ` appears only in the two
reviewed bridge calls. -/
theorem replay_real_add_gt_zero
    (W : World)
    {a b : ℂ}
    (ha : W.In a W.R)
    (hb : W.In b W.R)
    (ha0 : W.Gt a W.zero)
    (hb0 : W.Gt b W.zero) :
    W.Gt (W.add a b) W.zero := by
  /- First unwrap the two Litex order facts. The public relation `Gt` itself
  remains opaque; this is exactly the adapter-owned elimination theorem. -/
  rcases API.gt_zero_to_real W ha ha0 with ⟨ar, har, harPos⟩
  rcases API.gt_zero_to_real W hb hb0 with ⟨br, hbr, hbrPos⟩

  /- This is the only Mathlib step in the rule. The rule is not an axiom in
  generated Lean: it is the ordinary ordered-ring theorem `add_pos`. -/
  have hsum : 0 < ar + br := add_pos harPos hbrPos

  /- `same_add_real` is the checked complex/arithmetic congruence bridge.
  It says that the Litex operation has the native representative `ar + br`. -/
  have hadd : W.Same (W.add a b) ((ar + br : ℝ) : ℂ) :=
    W.same_add_real har hbr

  /- Finally wrap the native result into the same Litex relation that appeared
  in the source conclusion. No `RealPos` proposition is leaked to callers. -/
  exact API.gt_zero_of_real W (W.add_mem_R ha hb) ⟨ar + br, hadd, hsum⟩

/- The compiler's certificate is metadata; it does not replace the proof.
The child order is fixed to source order and can be checked before replay. -/
def certificate : Evidence RuleId.realAddGtZero :=
  { sourceRule := "builtin.order.real_add_gt_zero"
    childFactIds := ["in-a-R", "in-b-R", "gt-a-zero", "gt-b-zero"] }

end Tracer

end LitexSemanticsInLean

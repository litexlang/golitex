import LitexGenerate

/-!
This file is the handwritten Mathlib-facing layer. `LitexGenerate.lean` is
compiler-owned; this module consumes its declarations without modifying them.
-/

namespace ConvergenceScalingPipeline

open Filter Topology

abbrev LitexRealSequence := Litex.Fn Litex.N Litex.R

/-- A Mathlib index carrying exactly the heterogeneous natural-number input
accepted by a generated Litex function. Its order is the order of the
verifier-selected exact natural representative. -/
structure NaturalInput where
  value : ℂ
  membership : Litex.In value Litex.N

noncomputable def NaturalInput.natural (n : NaturalInput) : ℕ :=
  Litex.In.rep n.value n.membership

noncomputable instance : LE NaturalInput where
  le left right := left.natural ≤ right.natural

noncomputable instance : Preorder NaturalInput where
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans

noncomputable instance : IsDirectedOrder NaturalInput where
  directed left right := by
    by_cases h : left.natural ≤ right.natural
    · exact ⟨right, h, Nat.le_refl _⟩
    · refine ⟨left, Nat.le_refl _, ?_⟩
      change right.natural ≤ left.natural
      exact Nat.le_of_lt (Nat.lt_of_not_ge h)

instance : Nonempty NaturalInput :=
  ⟨{ value := (0 : ℂ)
     membership := Litex.Rules.complexEqNatInN 0 0 (by norm_num) }⟩

def toMathlibSequence (s : LitexRealSequence) : NaturalInput → ℝ :=
  fun n => s.call n.value n.membership

def scaleSequence (c : ℝ) (s : LitexRealSequence) : LitexRealSequence :=
  { call := fun {_} n hn => c * s.call n hn }

theorem tendsto_of_generated_convergesTo
    (s : LitexRealSequence)
    (a : ℝ)
    (h : __Compiler_main.converges_to s a) :
    Tendsto (toMathlibSequence s) atTop (nhds a) := by
  rw [Metric.tendsto_nhds]
  intro epsilon epsilonPositive
  let epsilonCarrier : Litex.RPos.Carrier := ⟨epsilon, epsilonPositive⟩
  obtain ⟨N0, N0In, close⟩ :=
    h.2.2 epsilonCarrier (Litex.In.own Litex.RPos epsilonCarrier)
  unfold __Compiler_main.is_eventually_close at close
  rcases close with ⟨_, _, _, _, tail⟩
  apply Filter.eventually_atTop.mpr
  refine ⟨⟨N0, N0In⟩, ?_⟩
  intro n hn
  have sourceTail := tail n.value n.membership (by
    exact Litex.OrderBridge.leOfReal (by exact_mod_cast hn))
  simpa [epsilonCarrier, toMathlibSequence, Litex.fnApplyOwn, Litex.Lt,
    Litex.OrderValue, Litex.abs, Real.dist_eq, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using sourceTail

theorem tendsto_mul_const_from_generated
    {alpha : Type 1}
    (s : alpha)
    (sIn : Litex.In s (Litex.fnSet Litex.N Litex.R))
    (a c : ℂ)
    (aIn : Litex.In a Litex.R)
    (cIn : Litex.In c Litex.R)
    (h : __Compiler_main.converges_to
      (Litex.In.rep s sIn) (Litex.In.rep a aIn)) :
    Tendsto
      (toMathlibSequence
        (scaleSequence (Litex.In.rep c cIn) (Litex.In.rep s sIn)))
      atTop
      (nhds (Litex.In.rep c cIn * Litex.In.rep a aIn)) := by
  have generated :=
    __Compiler_main.converges_to_mul_const s sIn a aIn c cIn h
  have generatedScaled :
      __Compiler_main.converges_to
        (scaleSequence (Litex.In.rep c cIn) (Litex.In.rep s sIn))
        (Litex.In.rep c cIn * Litex.In.rep a aIn) := by
    simpa [scaleSequence, Litex.fnApplyOwn] using generated
  exact tendsto_of_generated_convergesTo _ _ generatedScaled

end ConvergenceScalingPipeline

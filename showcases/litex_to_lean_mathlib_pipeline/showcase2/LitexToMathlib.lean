import LitexGenerate

/-!
This file is the handwritten Mathlib-facing layer. `LitexGenerate.lean` is
compiler-owned; this module consumes its declarations without modifying them.
-/

namespace ConvergenceScalingPipeline

open Filter Topology

abbrev LitexRealSequence := Litex.Fn Litex.N Litex.R

def toMathlibSequence (s : LitexRealSequence) : ℕ → ℝ :=
  fun n => s.call n (Litex.In.own Litex.N n)

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
  refine ⟨N0, ?_⟩
  intro n hn
  have hnExact :
      N0 ≤ Litex.In.rep n (Litex.In.own Litex.N n) := by
    rw [Litex.In.rep_exact (set := Litex.N) n (Litex.In.own Litex.N n)]
    exact hn
  have sourceTail := tail n (Litex.In.own Litex.N n) (by
    exact Litex.OrderBridge.leOfReal (by exact_mod_cast hnExact))
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
    __Compiler_main.converges_to_mul_const
      (Litex.In.rep s sIn)
      (Litex.In.own (Litex.fnSet Litex.N Litex.R) (Litex.In.rep s sIn))
      (Litex.In.rep a aIn)
      (Litex.In.own Litex.R (Litex.In.rep a aIn))
      (Litex.In.rep c cIn)
      (Litex.In.own Litex.R (Litex.In.rep c cIn))
      h
  have generatedScaled :
      __Compiler_main.converges_to
        (scaleSequence (Litex.In.rep c cIn) (Litex.In.rep s sIn))
        (Litex.In.rep c cIn * Litex.In.rep a aIn) := by
    simpa [scaleSequence, Litex.fnApply, Litex.fnApplyOwn] using generated
  exact tendsto_of_generated_convergesTo _ _ generatedScaled

end ConvergenceScalingPipeline

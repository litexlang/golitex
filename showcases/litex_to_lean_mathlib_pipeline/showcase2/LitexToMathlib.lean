import LitexGenerate

/-!
This file is the handwritten Mathlib-facing layer. `LitexGenerate.lean` is
compiler-owned; this module consumes its declarations without modifying them.
-/

namespace CauchySequencePipeline

open Filter Topology

abbrev LitexRealSequence := Litex.Rules.RealSequence

def toMathlibSequence (a : LitexRealSequence) : ℕ → ℝ :=
  Litex.Rules.realSequenceAt a

theorem cauchySeq_of_litexCauchy
    (a : LitexRealSequence)
    (h : Litex.Rules.RealSequenceCauchy a) :
    CauchySeq (toMathlibSequence a) := by
  rw [Metric.cauchySeq_iff]
  intro epsilon epsilonPositive
  obtain ⟨start, tail⟩ := h epsilon epsilonPositive
  exact ⟨start, fun m hm n hn => tail m n hm hn⟩

theorem tendsTo_of_litexConvergesTo
    (a : LitexRealSequence)
    (limit : ℝ)
    (h : Litex.Rules.RealSequenceConvergesTo a limit) :
    Tendsto (toMathlibSequence a) atTop (nhds limit) := by
  exact Metric.tendsto_atTop.mpr h

theorem mathlibCompleteness
    (a : LitexRealSequence)
    (h : Litex.Rules.RealSequenceCauchy a) :
    ∃ limit : ℝ, Tendsto (toMathlibSequence a) atTop (nhds limit) := by
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_litexCauchy a h)

/-- Mathlib completeness, stated with the predicates generated from `main.lit`. -/
theorem mathlibCompletenessInGeneratedVocabulary
    (a : LitexRealSequence)
    (h : __Compiler_main.is_cauchy_sequence a) :
    __Compiler_main.is_convergent_sequence a := by
  unfold __Compiler_main.is_cauchy_sequence at h
  rcases h with ⟨sequenceIn, nativeCauchy⟩
  unfold __Compiler_main.is_convergent_sequence
  refine ⟨sequenceIn, ?_⟩
  obtain ⟨limit, tends⟩ :=
    mathlibCompleteness (Litex.In.rep a sequenceIn) nativeCauchy
  exact ⟨limit, Metric.tendsto_atTop.mp tends⟩

end CauchySequencePipeline

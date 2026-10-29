import examples.function_limit_unique.statement

open Filter
open scoped Topology

namespace Adapter

private noncomputable abbrev model := Litex.NumericModel.model

private noncomputable def decodeReal (x : model.Value) : ℝ := by
  classical
  exact if h : ∃ r : ℝ, x = model.number (r : ℂ) then Classical.choose h else 0

private theorem decodeReal_number (r : ℝ) : decodeReal (model.number (r : ℂ)) = r := by
  classical
  have h : ∃ s : ℝ, model.number (r : ℂ) = model.number (s : ℂ) := ⟨r, rfl⟩
  have hs : Classical.choose h = r :=
    (Complex.ofReal_injective (model.number_injective (Classical.choose_spec h))).symm
  unfold decodeReal
  rw [dif_pos h, hs]

private noncomputable def signature : Litex.FunctionSignature model :=
  Litex.FunctionSignature.one .real .real (fun _ => True)

private noncomputable def body (f : ℝ → ℝ) (x : model.Value) : model.Value :=
  model.number (f (decodeReal x) : ℂ)

private noncomputable def function (f : ℝ → ℝ) :=
  Litex.formulaFnOn signature (body f) (by
    intro x _
    exact (model.real_members _).mpr ⟨f (decodeReal x), rfl⟩)

private theorem function_mem (f : ℝ → ℝ) :
    Litex.In (function f) (Litex.fnSet signature) := Litex.formulaFnInFnSet (function f)

private theorem function_domain (f : ℝ → ℝ) :
    Litex.FunctionSemantics.domainValue (Litex.denote (function f)) =
      Litex.denote (Litex.R (M := model)) := by
  have hraw := Litex.unguardedFunctionDomain (function f)
    (Litex.denote (Litex.R (M := model))) (Litex.denote (Litex.R (M := model)))
    (Litex.isSet (Litex.R (M := model))) (Litex.isSet (Litex.R (M := model))) (function_mem f)
  exact Litex.FunctionSemantics.domainValue_eq (Litex.isSet (Litex.R (M := model))) hraw

private theorem function_call (f : ℝ → ℝ) (x : ℝ) :
    Litex.FunctionSemantics.callValue (Litex.denote (function f)) (model.number (x : ℂ)) =
      model.number (f x : ℂ) := by
  have hx : model.mem (model.number (x : ℂ)) signature.domain := by
    change model.mem (model.number (x : ℂ))
      (Litex.SetSemantics.sepValue (model.standard .real) (fun _ => True))
    exact (Litex.SetSemantics.sep_members _ _ _).mpr
      ⟨(model.real_members _).mpr ⟨x, rfl⟩, True.intro⟩
  have call := Litex.FunctionSemantics.call_graphValue signature.domain signature.output
    (body f) (function f).wd (model.number (x : ℂ)) hx
  change Litex.FunctionSemantics.callValue (Litex.denote (function f))
    (model.number (x : ℂ)) = body f (model.number (x : ℂ)) at call
  simpa only [body, decodeReal_number] using call

private theorem nativeLimit_to_Litex (f : ℝ → ℝ) (x0 L : ℝ)
    (h : Tendsto f (𝓝[≠] x0) (𝓝 L)) :
    Litex.HasFiniteFunctionLimit .both (function f)
      (Litex.number (M := model) (x0 : ℂ)) (Litex.number (M := model) (L : ℂ)) := by
  refine ⟨x0, L, rfl, rfl, ?_, ?_⟩
  · intro radius hradius
    refine ⟨x0 + radius / 2, ?_, ?_, ?_⟩
    · rw [function_domain]
      exact (model.real_members _).mpr ⟨x0 + radius / 2, rfl⟩
    · dsimp [Litex.finiteLimitDistance]
      rw [show x0 + radius / 2 - x0 = radius / 2 by ring, abs_of_pos (by linarith)]
      linarith
    · dsimp [Litex.finiteLimitDistance]
      rw [show x0 + radius / 2 - x0 = radius / 2 by ring, abs_of_pos (by linarith)]
      linarith
  · intro epsilon hepsilon
    obtain ⟨delta, hdelta, hbound⟩ := (Metric.tendsto_nhdsWithin_nhds.mp h) epsilon hepsilon
    refine ⟨delta, hdelta, ?_⟩
    intro x _ hpositive hnear
    refine ⟨f x, function_call f x, ?_⟩
    have hne : x ≠ x0 := sub_ne_zero.mp (abs_pos.mp hpositive)
    have bound := hbound (x := x) (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne)
      (by simpa only [Litex.finiteLimitDistance, Real.dist_eq] using hnear)
    simpa only [Real.dist_eq] using bound

/-- This native theorem consumes the compiler-generated uniqueness proof. -/
theorem functionLimitsUnique (f : ℝ → ℝ) (x0 L K : ℝ)
    (hL : Tendsto f (𝓝[≠] x0) (𝓝 L)) (hK : Tendsto f (𝓝[≠] x0) (𝓝 K)) : L = K := by
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_unique_x2f_statement_x2e_lit.h_4
    (M := model) (function f) (function_mem f)
    (Litex.number (M := model) (x0 : ℂ)) (Litex.NativeBridge.numberInR x0)
    (Litex.number (M := model) (L : ℂ)) (Litex.NativeBridge.numberInR L)
    (Litex.number (M := model) (K : ℂ)) (Litex.NativeBridge.numberInR K)
    (nativeLimit_to_Litex f x0 L hL) (nativeLimit_to_Litex f x0 K hK)
  exact Complex.ofReal_injective (Litex.NativeBridge.complexEq generated)

end Adapter

import examples.function_limit_punctured_cancellation.statement

open Filter
open scoped Topology

namespace Adapter

private noncomputable abbrev model := Litex.NumericModel.model
private noncomputable abbrev sourceFunction :=
  LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_punctured_x5f_cancellation_x2f_statement_x2e_lit._object_i1 (M := model)

private theorem input_mem (x : ℝ) (hx : x ≠ 0) :
    model.mem (model.number (x : ℂ)) sourceFunction.val.signature.domain := by
  apply (Litex.FunctionSignature.oneTarget_domain _ _ _ _ _).mpr
  refine ⟨(model.real_members _).mpr ⟨x, rfl⟩, ?_⟩
  intro h
  exact hx (Complex.ofReal_injective (model.number_injective h))

private theorem function_call (x : ℝ) (hx : x ≠ 0) :
    Litex.FunctionSemantics.callValue (Litex.denote sourceFunction) (model.number (x : ℂ)) =
      model.number ((x ^ 2 / x : ℝ) : ℂ) := by
  have h := Litex.FunctionSemantics.call_graphValue sourceFunction.val.signature.domain
    sourceFunction.val.signature.target sourceFunction.val.bodyValue sourceFunction.wd
    (model.number (x : ℂ)) (input_mem x hx)
  change Litex.FunctionSemantics.callValue (Litex.denote sourceFunction)
    (model.number (x : ℂ)) = sourceFunction.val.bodyValue (model.number (x : ℂ)) at h
  rw [h]
  change model.divValue (model.powValue (model.number (x : ℂ)) (model.number (2 : ℂ)))
    (model.number (x : ℂ)) = _
  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, model.pow_numbers_nat,
    model.div_numbers _ _ (by exact_mod_cast hx), ← Complex.ofReal_pow, ← Complex.ofReal_div]

/-- The epsilon estimate comes from the compiled Litex proof. -/
theorem puncturedCancellationLimit :
    Tendsto (fun x : ℝ => x ^ 2 / x) (𝓝[≠] 0) (𝓝 0) := by
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_punctured_x5f_cancellation_x2f_statement_x2e_lit.h_33384 (M := model)
  obtain ⟨point, value, hpoint, hvalue, _, hestimate⟩ := generated
  have hp : point = 0 := (Complex.ofReal_injective (model.number_injective hpoint)).symm
  have hv : value = 0 := (Complex.ofReal_injective (model.number_injective hvalue)).symm
  subst point
  subst value
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hcontrol⟩ := hestimate epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro x hx hnear
  have hx0 : x ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  have hdomain := Litex.FunctionSemantics.domainValue_eq sourceFunction.val.signature.domain_isSet
    (Litex.formulaFnInFnSet sourceFunction)
  have hxD : model.mem (model.number (x : ℂ))
      (Litex.FunctionSemantics.domainValue (Litex.denote sourceFunction)) :=
    hdomain ▸ input_mem x hx0
  obtain ⟨output, houtput, hclose⟩ := hcontrol x hxD
    (by simpa only [Litex.finiteLimitDistance, sub_zero] using abs_pos.mpr hx0)
    (by simpa only [Litex.finiteLimitDistance, Real.dist_eq] using hnear)
  have houtput_eq : x ^ 2 / x = output :=
    Complex.ofReal_injective (model.number_injective ((function_call x hx0).symm.trans houtput))
  simpa only [Real.dist_eq, houtput_eq] using hclose

end Adapter

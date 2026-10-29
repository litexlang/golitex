import examples.function_limit_polynomial_chain.statement

open Filter
open scoped Topology

namespace Adapter

private noncomputable abbrev model := Litex.NumericModel.model
private noncomputable abbrev sourceFunction :=
  LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_polynomial_x5f_chain_x2f_statement_x2e_lit._object_i13 (M := model)

private theorem input_mem (x : ℝ) :
    model.mem (model.number (x : ℂ)) sourceFunction.val.signature.domain := by
  change model.mem (model.number (x : ℂ))
    (Litex.SetSemantics.sepValue (model.standard .real) (fun _ => True))
  exact (Litex.SetSemantics.sep_members _ _ _).mpr
    ⟨(model.real_members _).mpr ⟨x, rfl⟩, True.intro⟩

private theorem function_call (x : ℝ) :
    Litex.FunctionSemantics.callValue (Litex.denote sourceFunction) (model.number (x : ℂ)) =
      model.number (((x^2+1)*(x-2) : ℝ) : ℂ) := by
  have h := Litex.FunctionSemantics.call_graphValue sourceFunction.val.signature.domain
    sourceFunction.val.signature.target sourceFunction.val.bodyValue sourceFunction.wd
    (model.number (x : ℂ)) (input_mem x)
  change Litex.FunctionSemantics.callValue (Litex.denote sourceFunction)
    (model.number (x : ℂ)) = sourceFunction.val.bodyValue (model.number (x : ℂ)) at h
  rw [h]
  change model.mulValue (model.addValue
    (model.powValue (model.number (x : ℂ)) (model.number (2 : ℂ))) (model.number 1))
    (model.subValue (model.number (x : ℂ)) (model.number 2)) = _
  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, model.pow_numbers_nat,
    model.add_numbers, model.sub_numbers, model.mul_numbers]
  congr 1
  push_cast
  ring

/-- The limit estimate is the result of the generated chain of limit rules. -/
theorem polynomialChainLimit :
    Tendsto (fun x : ℝ => (x^2+1)*(x-2)) (𝓝[≠] 2) (𝓝 0) := by
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_polynomial_x5f_chain_x2f_statement_x2e_lit.h_47854 (M := model)
  obtain ⟨point, value, hpoint, hvalue, _, hestimate⟩ := generated
  have hp : point = 2 := (Complex.ofReal_injective (model.number_injective hpoint)).symm
  have hv : value = 0 := (Complex.ofReal_injective (model.number_injective hvalue)).symm
  subst point
  subst value
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hcontrol⟩ := hestimate epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro x hx hnear
  have hx2 : x ≠ 2 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  have hdomain := Litex.FunctionSemantics.domainValue_eq sourceFunction.val.signature.domain_isSet
    (Litex.formulaFnInFnSet sourceFunction)
  have hxD : model.mem (model.number (x : ℂ))
      (Litex.FunctionSemantics.domainValue (Litex.denote sourceFunction)) := hdomain ▸ input_mem x
  obtain ⟨output, houtput, hclose⟩ := hcontrol x hxD
    (by simpa only [Litex.finiteLimitDistance] using abs_pos.mpr (sub_ne_zero.mpr hx2))
    (by simpa only [Litex.finiteLimitDistance, Real.dist_eq] using hnear)
  have houtput_eq : (x^2+1)*(x-2) = output :=
    Complex.ofReal_injective (model.number_injective ((function_call x).symm.trans houtput))
  simpa only [Real.dist_eq, houtput_eq] using hclose

end Adapter

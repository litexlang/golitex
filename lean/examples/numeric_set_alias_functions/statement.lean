import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_numeric_x5f_set_x5f_alias_x5f_functions_x2f_statement_x2e_lit

universe u v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.R (M := M))
theorem h_3 : Litex.IsSet (_object_i1 (M := M)) :=
  (Litex.isSet (Litex.R (M := M)))
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (Litex.sameRefl (Litex.R (M := M)))

noncomputable def _object_i2 := (_object_i1 (M := M))
theorem h_5 : Litex.Same (_object_i2 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
  intro _raw_i4 h_55 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_55)
  have h_55 : Litex.In _value_i4 (_object_i1 (M := M)) := h_55
  change Litex.In _value_i4 (_object_i2 (M := M))
  exact (Litex.inOfSame _value_i4 _value_i4 (_object_i1 (M := M)) (_object_i2 (M := M)) (Litex.sameRefl _value_i4) (((Litex.sameRefl (_object_i1 (M := M)))).trans ((h_5 (M := M))).symm) h_55)))
theorem h_62 : Litex.In (_object_i3 (M := M)) (by
  have _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := by
    intro _raw_i4 h_61 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_61)
    have h_61 : Litex.In _value_i4 (_object_i1 (M := M)) := h_61
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_63 : Litex.Same (_object_i3 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
  intro _raw_i4 h_55 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_55)
  have h_55 : Litex.In _value_i4 (_object_i1 (M := M)) := h_55
  change Litex.In _value_i4 (_object_i2 (M := M))
  exact (Litex.inOfSame _value_i4 _value_i4 (_object_i1 (M := M)) (_object_i2 (M := M)) (Litex.sameRefl _value_i4) (((Litex.sameRefl (_object_i1 (M := M)))).trans ((h_5 (M := M))).symm) h_55))) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_64 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_62 (M := M)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) True.intro) (Litex.number (M := M) (2 : ℂ)) :=
  (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))) = (M.number (2 : ℂ)) from by
    let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_62 (M := M)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) True.intro)
    let _litex_formula := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
    intro _raw_i4 h_55 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_55)
    have h_55 : Litex.In _value_i4 (_object_i1 (M := M)) := h_55
    change Litex.In _value_i4 (_object_i2 (M := M))
    exact (Litex.inOfSame _value_i4 _value_i4 (_object_i1 (M := M)) (_object_i2 (M := M)) (Litex.sameRefl _value_i4) (((Litex.sameRefl (_object_i1 (M := M)))).trans ((h_5 (M := M))).symm) h_55)))
    have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (((Litex.sameRefl (_object_i3 (M := M)))).trans (h_63 (M := M)))
    have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _).mpr _litex_original.wd.2)
    exact _litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.number (2 : ℂ)) from rfl))
  )).trans (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))))

def prop_5 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) : Prop :=
  ∃ (h_137 : Litex.In _value_i5 (_object_i1 (M := M))), ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))

noncomputable def _object_i7 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i8)) (by
  intro _raw_i8 h_204 h_138
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_204)
  have h_204 : Litex.In _value_i8 (_object_i2 (M := M)) := h_204
  have h_138 : ((prop_5 (M := M)) _value_i8) :=
    (by
      change (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))
      exact h_138)
  have h_205 : Litex.In _value_i8 (_object_i1 (M := M)) :=
    (by rcases h_138 with ⟨h_137, h_136⟩; exact h_137)
  have h_208 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
    (by rcases h_138 with ⟨h_137, h_136⟩; exact h_136)
  change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (_object_i1 (M := M))
  exact (Litex.inOfSame (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208)) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204) ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208)).wd.2.2))))
theorem h_341 : Litex.In (_object_i7 (M := M)) (by
  have _checked_header : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) _raw_i8) → True := by
    intro _raw_i8 h_336 h_138
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_336)
    have h_336 : Litex.In _value_i8 (_object_i2 (M := M)) := h_336
    have h_138 : ((prop_5 (M := M)) _value_i8) :=
      (by
        change (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))
        exact h_138)
    have h_337 : Litex.In _value_i8 (_object_i1 (M := M)) :=
      (by rcases h_138 with ⟨h_137, h_136⟩; exact h_137)
    have h_340 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
      (by rcases h_138 with ⟨h_137, h_136⟩; exact h_136)
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))))) :=
  (Litex.formulaFnInFnSet (_object_i7 (M := M)))
theorem h_342 : Litex.Same (_object_i7 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i8)) (by
  intro _raw_i8 h_204 h_138
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_204)
  have h_204 : Litex.In _value_i8 (_object_i2 (M := M)) := h_204
  have h_138 : ((prop_5 (M := M)) _value_i8) :=
    (by
      change (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))
      exact h_138)
  have h_205 : Litex.In _value_i8 (_object_i1 (M := M)) :=
    (by rcases h_138 with ⟨h_137, h_136⟩; exact h_137)
  have h_208 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
    (by rcases h_138 with ⟨h_137, h_136⟩; exact h_136)
  change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (_object_i1 (M := M))
  exact (Litex.inOfSame (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208)) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204) ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208)).wd.2.2)))) :=
  (Litex.sameRefl (_object_i7 (M := M)))

theorem h_343 : ((prop_5 (M := M)) (Litex.number (M := M) (2 : ℂ))) :=
  (Exists.intro (Litex.inOfSame (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_62 (M := M)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) True.intro) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (_object_i1 (M := M)) ((((Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))).trans ((h_64 (M := M))).symm)).symm (Litex.sameRefl (_object_i1 (M := M))) (Litex.inOfSame (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_62 (M := M)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_62 (M := M)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) True.intro) (_object_i2 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_62 (M := M)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) True.intro)) (((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_62 (M := M)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) True.intro)))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_366 : Litex.In (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) :=
  (by rcases (h_343 (M := M)) with ⟨h_137, h_136⟩; exact h_137)

theorem h_369 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (by rcases (h_343 (M := M)) with ⟨h_137, h_136⟩; exact h_136)

theorem h_370 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) (_object_i7 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_341 (M := M)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (_object_i2 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans ((h_5 (M := M))).symm) (h_366 (M := M))) (h_343 (M := M))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (h_369 (M := M))) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) (_object_i7 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_341 (M := M)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (_object_i2 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans ((h_5 (M := M))).symm) (h_366 (M := M))) (h_343 (M := M)))
    let _litex_literal := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i8)) (by
      intro _raw_i8 h_204 h_138
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_204)
      have h_204 : Litex.In _value_i8 (_object_i2 (M := M)) := h_204
      have h_138 : ((prop_5 (M := M)) _value_i8) :=
        (by
          change (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))
          exact h_138)
      have h_205 : Litex.In _value_i8 (_object_i1 (M := M)) :=
        (by rcases h_138 with ⟨h_137, h_136⟩; exact h_137)
      have h_208 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
        (by rcases h_138 with ⟨h_137, h_136⟩; exact h_136)
      change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (_object_i1 (M := M))
      exact (Litex.inOfSame (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208)) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204) ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208)).wd.2.2)))) (Litex.number (M := M) (2 : ℂ)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i8)) (by
      intro _raw_i8 h_204 h_138
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_204)
      have h_204 : Litex.In _value_i8 (_object_i2 (M := M)) := h_204
      have h_138 : ((prop_5 (M := M)) _value_i8) :=
        (by
          change (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))
          exact h_138)
      have h_205 : Litex.In _value_i8 (_object_i1 (M := M)) :=
        (by rcases h_138 with ⟨h_137, h_136⟩; exact h_137)
      have h_208 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
        (by rcases h_138 with ⟨h_137, h_136⟩; exact h_136)
      change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (_object_i1 (M := M))
      exact (Litex.inOfSame (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208)) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204) ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.sameRefl _value_i8) (((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_5 (M := M)))).trans (h_4 (M := M))) h_204)) h_208)).wd.2.2))))) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (_object_i2 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans ((h_5 (M := M))).symm) (h_366 (M := M))) (h_343 (M := M)))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i7 (M := M)))).trans (h_342 (M := M))) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i8)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i8)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from rfl))
  ))).trans (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (h_369 (M := M)))))
end LitexCompiled.file_lean_x2f_examples_x2f_numeric_x5f_set_x5f_alias_x5f_functions_x2f_statement_x2e_lit

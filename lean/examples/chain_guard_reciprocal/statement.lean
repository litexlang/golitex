import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_chain_x5f_guard_x5f_reciprocal_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) : Prop :=
  ∃ (h_2 : Litex.In _value_i1 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1) ∧ (Litex.Lt _value_i1 (Litex.number (M := M) (1 : ℂ))))

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_65 h_35
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_65)
  have h_65 : Litex.In _value_i4 (Litex.R (M := M)) := h_65
  have h_35 : ((prop_1 (M := M)) _value_i4) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))
            exact h_35)
        )
    )
  have h_66 :=
    (Classical.choose (show ((prop_1 (M := M)) _value_i4) from h_35))
  have h_67 : ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4) ∧ (Litex.Lt _value_i4 (Litex.number (M := M) (1 : ℂ)))) :=
    (by
      litex_checked_step =>
        exact (
          (by rcases h_35 with ⟨h_2, h_1⟩; exact h_1)
        )
    )
  have h_68 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
    (by
      litex_checked_step =>
        exact (
          (And.left (by rcases h_35 with ⟨h_2, h_1⟩; exact h_1))
        )
    )
  have h_69 : Litex.Lt _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (And.right (by rcases h_35 with ⟨h_2, h_1⟩; exact h_1))
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_65) (fun _litex_equal => (Litex.ltNotSame (Litex.number (M := M) (0 : ℂ)) _value_i4 h_68) _litex_equal.symm))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_65) (fun _litex_equal => (Litex.ltNotSame (Litex.number (M := M) (0 : ℂ)) _value_i4 h_68) _litex_equal.symm))
    exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_65 (_atomic_wd_1_0).wd.2.2))))
theorem h_153 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_154 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_155 : (by
  let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact ((prop_1 (M := M)) _atomic_wd_1_0)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
          exact (Exists.intro (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) (And.intro (by
            let _atomic_wd_2_1 := _atomic_wd_1_0
            exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
              let _atomic_wd_3_0 := _atomic_wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2.1 (_atomic_wd_3_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_2_1 (by
              let _atomic_wd_3_0 := _atomic_wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2.1 (_atomic_wd_3_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (2 : ℝ)) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_1 (by
              let _atomic_wd_3_0 := _atomic_wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2.1 (_atomic_wd_3_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact ((Litex.NativeBridge.lt_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (1 : ℂ)) (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2.1 (_atomic_wd_3_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2.1 (_atomic_wd_3_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (2 : ℝ)) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2.1 (_atomic_wd_3_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))))
      )
  )

theorem h_230 : Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_155 (M := M)) with ⟨h_2, h_1⟩; exact h_2)
      )
  )

theorem h_231 : ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) ∧ (Litex.Lt (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (Litex.number (M := M) (1 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_155 (M := M)) with ⟨h_2, h_1⟩; exact h_1)
      )
  )

theorem h_232 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (And.left (by rcases (h_155 (M := M)) with ⟨h_2, h_1⟩; exact h_1))
      )
  )

theorem h_233 : Litex.Lt (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (And.right (by rcases (h_155 (M := M)) with ⟨h_2, h_1⟩; exact h_1))
      )
  )

noncomputable def _object_w11 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))) (_object_i3 (M := M)) _wd_1_0 (h_153 (M := M)) (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (h_230 (M := M))) (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (h_155 (M := M)))))

theorem h_234 : (by
  let _equal_wd_1_0 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w11 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) = (M.number (2 : ℂ)) from by
          have _litex_residual : (M.divValue (M.number (1 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) = (M.number (2 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (_equal_wd_1_0).val.argument;
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (2 : ℂ))))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) ((1 : ℂ) / ((1 : ℂ) / (2 : ℂ))) (2 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))))).trans (by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _wd_1_1 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (h_230 (M := M))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (h_155 (M := M)))))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_154 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) from rfl))
        ))).trans _litex_residual)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_chain_x5f_guard_x5f_reciprocal_x2f_statement_x2e_lit

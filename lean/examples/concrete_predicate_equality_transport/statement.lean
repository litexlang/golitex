import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_concrete_x5f_predicate_x5f_equality_x5f_transport_x2f_statement_x2e_lit

universe u v1 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) : Prop :=
  ∃ (h_2 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
  intro _raw_i4 h_71 h_41
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_71)
  have h_71 : Litex.In _value_i4 (Litex.R (M := M)) := h_71
  have h_41 : ((prop_1 (M := M)) _value_i4) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))
            exact h_41)
        )
    )
  have h_72 :=
    (Classical.choose (show ((prop_1 (M := M)) _value_i4) from h_41))
  have h_73 :=
    (Classical.choose_spec (show ((prop_1 (M := M)) _value_i4) from h_41))
  change (by
    let _atomic_wd_1_0 := (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_71 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_71 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := h_71
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInR _litex_power _recorded_power_base
    ))))
theorem h_113 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_114 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_119 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_132 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_133 : Litex.In _value_i7 (Litex.R (M := M))) (h_115 : Litex.Same _value_i6 _value_i7) (h_116 : ((prop_1 (M := M)) _value_i6)), (by
  let _object_w9 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (_object_i3 (M := M)) _value_i7 (h_113 (M := M)) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) h_115 (show @Eq M.Value _ _ from Eq.refl _) h_132) (show ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i7)) from by
    have _known_citation : ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)) := h_116
    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) _known_value)) h_115)) _known_citation
  ))
  let _object_w10 := (Litex.powNatReal _value_i7 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) h_115 (show @Eq M.Value _ _ from Eq.refl _) h_132) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
  exact ((((prop_1 (M := M)) _value_i7)) ∧ ((by
    let _equal_wd_1_0 := _object_w9
    let _equal_wd_1_1 := _object_w10
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    intro _Host_i6 _rep_i6 _value_i6 h_132 _Host_i7 _rep_i7 _value_i7 h_133 h_115 h_116
    have h_134 :=
      (Classical.choose (show ((prop_1 (M := M)) _value_i6) from h_116))
    have h_135 :=
      (Classical.choose_spec (show ((prop_1 (M := M)) _value_i6) from h_116))
    have h_117 : ((prop_1 (M := M)) _value_i7) :=
      (by
        litex_checked_step =>
          exact (
            (show ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i7)) from by
              have _known_citation : ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)) := h_116
              exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) _known_value)) h_115)) _known_citation
            )
          )
      )
    have h_138 :=
      (Classical.choose (show ((prop_1 (M := M)) _value_i7) from h_117))
    have h_139 :=
      (Classical.choose_spec (show ((prop_1 (M := M)) _value_i7) from h_117))
    let _object_w9 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (_object_i3 (M := M)) _value_i7 (h_113 (M := M)) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) h_115 (show @Eq M.Value _ _ from Eq.refl _) h_132) (show ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i7)) from by
      have _known_citation : ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)) := h_116
      exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) _known_value)) h_115)) _known_citation
    ))
    let _object_w10 := (Litex.powNatReal _value_i7 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) h_115 (show @Eq M.Value _ _ from Eq.refl _) h_132) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    have h_118 : (by
      let _equal_wd_1_0 := _object_w9
      let _equal_wd_1_1 := _object_w10
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w9;
            let _equal_wd_1_1 := _object_w10;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i7)) = (M.powValue (Litex.denote _value_i7) (M.number (2 : ℂ))) from by
              have _litex_residual : (M.powValue (Litex.denote _value_i7) (M.number (2 : ℂ))) = (M.powValue (Litex.denote _value_i7) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i7)))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
              let _wd_1_1 := _value_i7;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inOfSame _value_i6 _wd_1_1 (Litex.R (M := M)) (Litex.R (M := M)) h_115 (show @Eq M.Value _ _ from Eq.refl _) h_132) (show ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _wd_1_1)) from by
                have _known_citation : ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)) := h_116
                exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) _known_value)) h_115)) _known_citation
              )))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_114 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (Litex.denote _value_i7) (M.number (2 : ℂ))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    exact (And.intro h_117 h_118)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_concrete_x5f_predicate_x5f_equality_x5f_transport_x2f_statement_x2e_lit

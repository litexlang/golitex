import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_shift_x5f_square_x5f_quotient_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (3 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (3 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (3 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (3 : ℂ)) h_14 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))))))
theorem h_53 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_54 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

theorem h_56 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_57 : Litex.In _value_i3 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_53 (M := M)) h_57 True.intro);
  let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_3_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  (Litex.neg _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.powObjInC _arithmetic))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.negInC _arithmetic.val.arg _arithmetic.wd)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
  let _equal_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_57 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  let _wd_4_1 := (Litex.mul (Litex.number (M := M) (6 : ℂ)) _value_i3 (Litex.numberInC (M := M) (6 : ℂ)) (M.real_subset_complex _ h_57));
  (Litex.add _wd_4_0 _wd_4_1 (by
    let _atomic_wd_1_0 := _wd_4_0
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (M.real_subset_complex _ h_57)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    )) (by
    let _atomic_wd_1_0 := _wd_4_1
    exact (Litex.mulInC (Litex.number (M := M) (6 : ℂ)) _value_i3 (Litex.numberInC (M := M) (6 : ℂ)) (M.real_subset_complex _ h_57)))));
  let _wd_3_1 := (Litex.number (M := M) (9 : ℂ));
  (Litex.add _wd_3_0 _wd_3_1 (by
    let _atomic_wd_1_0 := _wd_3_0
    exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
      let _litex_power := (_atomic_wd_1_0).val.left
      have _elaborated_power_base := (M.real_subset_complex _ h_57)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ) (Litex.mulInC (Litex.number (M := M) (6 : ℂ)) _value_i3 (Litex.numberInC (M := M) (6 : ℂ)) (M.real_subset_complex _ h_57)))) (Litex.numberInC (M := M) (9 : ℂ))));
  (Litex.neg _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (9 : ℂ)) (Litex.addInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (by
      let _litex_power := ((_atomic_wd_1_0).val.left).val.left
      have _elaborated_power_base := (M.real_subset_complex _ h_57)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ) (Litex.mulInC (Litex.number (M := M) (6 : ℂ)) _value_i3 (Litex.numberInC (M := M) (6 : ℂ)) (M.real_subset_complex _ h_57))) (Litex.numberInC (M := M) (9 : ℂ))))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.negInC (_atomic_wd_1_0).val.arg (Litex.addInC ((_atomic_wd_1_0).val.arg).val.left (Litex.number (M := M) (9 : ℂ)) (Litex.addInC (((_atomic_wd_1_0).val.arg).val.left).val.left (((_atomic_wd_1_0).val.arg).val.left).val.right (by
      let _litex_power := (((_atomic_wd_1_0).val.arg).val.left).val.left
      have _elaborated_power_base := (M.real_subset_complex _ h_57)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ) (Litex.mulInC (Litex.number (M := M) (6 : ℂ)) _value_i3 (Litex.numberInC (M := M) (6 : ℂ)) (M.real_subset_complex _ h_57))) (Litex.numberInC (M := M) (9 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_57
    have h_1597 : Litex.In _value_i3 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_57
          )
      )
    exact (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_53 (M := M)) h_1597 True.intro);
    let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_3_0
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    (Litex.neg _wd_2_0 (by
      let _atomic_wd_1_0 := _wd_2_0
      exact (by
        let _arithmetic := _atomic_wd_1_0
        exact Litex.powObjInC _arithmetic))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _arithmetic := _atomic_wd_1_0
        exact Litex.negInC _arithmetic.val.arg _arithmetic.wd)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
    let _equal_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1597 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_4_1 := (Litex.mul (Litex.number (M := M) (6 : ℂ)) _value_i3 (Litex.numberInC (M := M) (6 : ℂ)) (M.real_subset_complex _ h_1597));
    (Litex.add _wd_4_0 _wd_4_1 (by
      let _atomic_wd_1_0 := _wd_4_0
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (M.real_subset_complex _ h_1597)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (by
      let _atomic_wd_1_0 := _wd_4_1
      exact (Litex.mulInC (Litex.number (M := M) (6 : ℂ)) _value_i3 (Litex.numberInC (M := M) (6 : ℂ)) (M.real_subset_complex _ h_1597)))));
    let _wd_3_1 := (Litex.number (M := M) (9 : ℂ));
    (Litex.add _wd_3_0 _wd_3_1 (by
      let _atomic_wd_1_0 := _wd_3_0
      exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
        let _litex_power := (_atomic_wd_1_0).val.left
        have _elaborated_power_base := (M.real_subset_complex _ h_1597)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.mulInC (Litex.number (M := M) (6 : ℂ)) _value_i3 (Litex.numberInC (M := M) (6 : ℂ)) (M.real_subset_complex _ h_1597)))) (Litex.numberInC (M := M) (9 : ℂ))));
    (Litex.neg _wd_2_0 (by
      let _atomic_wd_1_0 := _wd_2_0
      exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (9 : ℂ)) (Litex.addInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (by
        let _litex_power := ((_atomic_wd_1_0).val.left).val.left
        have _elaborated_power_base := (M.real_subset_complex _ h_1597)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.mulInC (Litex.number (M := M) (6 : ℂ)) _value_i3 (Litex.numberInC (M := M) (6 : ℂ)) (M.real_subset_complex _ h_1597))) (Litex.numberInC (M := M) (9 : ℂ))))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.negInC (_atomic_wd_1_0).val.arg (Litex.addInC ((_atomic_wd_1_0).val.arg).val.left (Litex.number (M := M) (9 : ℂ)) (Litex.addInC (((_atomic_wd_1_0).val.arg).val.left).val.left (((_atomic_wd_1_0).val.arg).val.left).val.right (by
        let _litex_power := (((_atomic_wd_1_0).val.arg).val.left).val.left
        have _elaborated_power_base := (M.real_subset_complex _ h_1597)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.mulInC (Litex.number (M := M) (6 : ℂ)) _value_i3 (Litex.numberInC (M := M) (6 : ℂ)) (M.real_subset_complex _ h_1597))) (Litex.numberInC (M := M) (9 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((congrArg₂ M.divValue (congrArg M.negValue (congrArg₂ M.powValue (by
      let _litex_original := (((_equal_wd_1_0).val.left).val.arg).val.base
      let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
      let _wd_1_1 := _value_i3;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1597 True.intro))
      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (3 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (3 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i3) (M.number (3 : ℂ))) from rfl))
    ) (Eq.refl (M.number (2 : ℂ))))) (Eq.refl (M.number (2 : ℂ))))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.add _value_i3 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_1597) (Litex.numberInC (M := M) (3 : ℂ)));
    let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_3_0
      exact (Litex.addInR _value_i3 (Litex.number (M := M) (3 : ℂ)) h_1597 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    (Litex.neg _wd_2_0 (by
      let _atomic_wd_1_0 := _wd_2_0
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.addInC _value_i3 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_1597) (Litex.numberInC (M := M) (3 : ℂ)))
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.negInC (_atomic_wd_1_0).val.arg (by
        let _litex_power := (_atomic_wd_1_0).val.arg
        have _elaborated_power_base := (Litex.addInC _value_i3 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_1597) (Litex.numberInC (M := M) (3 : ℂ)))
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
    let _equal_wd_2_1 := _equal_wd_1_1;
    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (congrArg₂ M.divValue (show (M.negValue (M.powValue (M.addValue (Litex.denote _value_i3) (M.number (3 : ℂ))) (M.number (2 : ℂ)))) = (M.negValue (M.addValue (M.addValue (M.powValue (Litex.denote _value_i3) (M.number (2 : ℂ))) (M.mulValue (M.number (6 : ℂ)) (Litex.denote _value_i3))) (M.number (9 : ℂ)))) from (let _equal_wd_3_0 := (_equal_wd_2_0).val.left;
    let _equal_wd_3_1 := (_equal_wd_2_1).val.left;
    (show Litex.Same _equal_wd_3_0 _equal_wd_3_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (- (((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_1597)) + (3 : ℂ)) ^ (2 : ℕ))) (- ((((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_1597)) ^ (2 : ℕ)) + ((6 : ℂ) * (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_1597)))) + (9 : ℂ))) (Litex.NativeBridge.denoteNeg (_equal_wd_3_0).val.arg (_equal_wd_3_0).wd _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_3_0).val.arg).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
      let _atomic_wd_1_0 := ((_equal_wd_3_0).val.arg).val.base
      exact (Litex.addInR _value_i3 (Litex.number (M := M) (3 : ℂ)) h_1597 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteAdd _value_i3 (Litex.number (M := M) (3 : ℂ)) (((_equal_wd_3_0).val.arg).val.base).wd.1 (((_equal_wd_3_0).val.arg).val.base).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_1597)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))))) (Litex.NativeBridge.denoteNeg (_equal_wd_3_1).val.arg (_equal_wd_3_1).wd _ (Litex.NativeBridge.denoteAdd ((_equal_wd_3_1).val.arg).val.left (Litex.number (M := M) (9 : ℂ)) ((_equal_wd_3_1).val.arg).wd.1 ((_equal_wd_3_1).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteAdd (((_equal_wd_3_1).val.arg).val.left).val.left (((_equal_wd_3_1).val.arg).val.left).val.right (((_equal_wd_3_1).val.arg).val.left).wd.1 (((_equal_wd_3_1).val.arg).val.left).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1597 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_1597))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (6 : ℂ)) _value_i3 ((((_equal_wd_3_1).val.arg).val.left).val.right).wd.1 ((((_equal_wd_3_1).val.arg).val.left).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_1597)))) (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)))) (by ring!))))) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))))).trans ((Eq.refl (M.divValue (M.negValue (M.addValue (M.addValue (M.powValue (Litex.denote _value_i3) (M.number (2 : ℂ))) (M.mulValue (M.number (6 : ℂ)) (Litex.denote _value_i3))) (M.number (9 : ℂ)))) (M.number (2 : ℂ))))).symm))))
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_shift_x5f_square_x5f_quotient_x2f_statement_x2e_lit

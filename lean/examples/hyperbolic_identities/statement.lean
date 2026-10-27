import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_identities_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_10 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_23 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w3 := (let _wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i1 h_23);
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  let _wd_1_1 := (let _wd_2_0 := (Litex.sinh _value_i1 h_23);
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i1 h_23)
    exact (Litex.sinhInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i1 h_23);
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_2_0 := (Litex.cosh _value_i1 h_23)
      exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.coshInRPos (_atomic_wd_1_0).val.base))
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    )) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.sinh _value_i1 h_23);
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_2_0 := (Litex.sinh _value_i1 h_23)
      exact (Litex.sinhInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.base))
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))))
  let _object_w4 := (let _wd_1_0 := (Litex.cosh _value_i1 h_23);
  let _wd_1_1 := (Litex.sinh _value_i1 h_23);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i1 h_23)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))))
  let _object_w5 := (Litex.exp _value_i1 h_23)
  let _object_w6 := (let _wd_1_0 := (Litex.neg _value_i1 (M.real_subset_complex _ h_23));
  (Litex.exp _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.negInR _value_i1 h_23))))
  let _object_w7 := (let _wd_1_0 := (Litex.cosh _value_i1 h_23);
  let _wd_1_1 := (Litex.sinh _value_i1 h_23);
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i1 h_23)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))))
  let _object_w8 := (let _wd_1_0 := (Litex.tanh _value_i1 h_23);
  let _wd_1_1 := (Litex.cosh _value_i1 h_23);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.tanh _value_i1 h_23)
    exact (M.real_subset_complex _ (Litex.tanhInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0)))))
  let _object_w9 := (Litex.sinh _value_i1 h_23)
  let _object_w10 := (let _wd_1_0 := (Litex.sech _value_i1 h_23);
  let _wd_1_1 := (Litex.cosh _value_i1 h_23);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.sech _value_i1 h_23)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.sechInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0)))))
  let _object_w11 := (Litex.tanh _value_i1 h_23)
  let _object_w12 := (let _wd_1_0 := _object_w9;
  let _wd_1_1 := (Litex.sech _value_i1 h_23);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _object_w9
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.sech _value_i1 h_23)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.sechInRPos _atomic_wd_1_0)))))
  let _object_w13 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_1 := (let _wd_2_0 := _object_w11;
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _object_w11
    exact (Litex.tanhInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  (Litex.sub _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (M.real_subset_complex _ (Litex.tanhInR (_atomic_wd_1_0).val.base))
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))))
  let _object_w14 := (let _wd_1_0 := (Litex.sech _value_i1 h_23);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := (Litex.sech _value_i1 h_23)
    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.sechInRPos _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
  let _object_w15 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i1 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_23));
  (Litex.sinh _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInR (Litex.number (M := M) (2 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_23))))
  let _object_w16 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_2_1 := _object_w9;
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
    let _atomic_wd_1_0 := _object_w9
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))));
  let _wd_1_1 := (Litex.cosh _value_i1 h_23);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.right)))) (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0)))))
  let _object_w17 := (let _wd_1_0 := (_object_w15).val.arg;
  (Litex.cosh _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInR (Litex.number (M := M) (2 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_23))))
  let _object_w18 := (let _wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i1 h_23);
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  let _wd_1_1 := (let _wd_2_0 := _object_w9;
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _object_w9
    exact (Litex.sinhInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i1 h_23);
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_2_0 := (Litex.cosh _value_i1 h_23)
      exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.coshInRPos (_atomic_wd_1_0).val.base))
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    )) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.base))
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))))
  exact (((by
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w8
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w10
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))) ∧ ((((by
    let _equal_wd_1_0 := _object_w11
    let _equal_wd_1_1 := _object_w12
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w13
    let _equal_wd_1_1 := _object_w14
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w15
    let _equal_wd_1_1 := _object_w16
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w17
    let _equal_wd_1_1 := _object_w18
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_23
          let _object_w3 := (let _wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i1 h_23);
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
            exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (let _wd_2_0 := (Litex.sinh _value_i1 h_23);
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i1 h_23)
            exact (Litex.sinhInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i1 h_23);
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := (Litex.cosh _value_i1 h_23)
              exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.coshInRPos (_atomic_wd_1_0).val.base))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.sinh _value_i1 h_23);
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := (Litex.sinh _value_i1 h_23)
              exact (Litex.sinhInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.base))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))))
          have h_1 : (by
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w3;
                  (show Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1 (1 : ℂ) (((Real.cosh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) ^ (2 : ℕ)) - ((Real.sinh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) ^ (2 : ℕ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteSub (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_1).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _hyp := ((_equal_wd_1_1).val.left).val.base; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23))))) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_1).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (Litex.sinh _value_i1 h_23)
                    exact (Litex.sinhInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _hyp := ((_equal_wd_1_1).val.right).val.base; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23)))))) (by symm; exact (Litex.hyperbolicPythagorean ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re)))))
                )
            )
          let _object_w4 := (let _wd_1_0 := (Litex.cosh _value_i1 h_23);
          let _wd_1_1 := (Litex.sinh _value_i1 h_23);
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i1 h_23)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))))
          let _object_w5 := (Litex.exp _value_i1 h_23)
          have h_2 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    have _identity := Litex.expThroughHyperbolic ((_equal_wd_1_0).val.left).val.arg ((_equal_wd_1_0).val.left).wd
                    change ((Litex.realUnaryValue (M := M) Real.exp) (Litex.denote _value_i1)) = (M.addValue ((Litex.realUnaryValue (M := M) Real.cosh) (Litex.denote _value_i1)) ((Litex.realUnaryValue (M := M) Real.sinh) (Litex.denote _value_i1))) at _identity
                    exact _identity.symm)))
                )
            )
          let _object_w6 := (let _wd_1_0 := (Litex.neg _value_i1 (M.real_subset_complex _ h_23));
          (Litex.exp _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.negInR _value_i1 h_23))))
          let _object_w7 := (let _wd_1_0 := (Litex.cosh _value_i1 h_23);
          let _wd_1_1 := (Litex.sinh _value_i1 h_23);
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i1 h_23)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    have _identity := Litex.expNegativeThroughHyperbolic ((_equal_wd_1_1).val.left).val.arg ((_equal_wd_1_1).val.left).wd
                    change ((Litex.realUnaryValue (M := M) Real.exp) (M.negValue (Litex.denote _value_i1))) = (M.subValue ((Litex.realUnaryValue (M := M) Real.cosh) (Litex.denote _value_i1)) ((Litex.realUnaryValue (M := M) Real.sinh) (Litex.denote _value_i1))) at _identity
                    exact _identity)))
                )
            )
          let _object_w8 := (let _wd_1_0 := (Litex.tanh _value_i1 h_23);
          let _wd_1_1 := (Litex.cosh _value_i1 h_23);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.tanh _value_i1 h_23)
            exact (M.real_subset_complex _ (Litex.tanhInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0)))))
          let _object_w9 := (Litex.sinh _value_i1 h_23)
          have h_4 : (by
            let _equal_wd_1_0 := _object_w8
            let _equal_wd_1_1 := _object_w9
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w8;
                  let _equal_wd_1_1 := _object_w9;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((Real.tanh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) * (Real.cosh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ)) (Real.sinh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _hyp := (_equal_wd_1_0).val.left; Litex.denoteTanh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23)))) (let _hyp := (_equal_wd_1_0).val.right; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23))))) (let _hyp := _equal_wd_1_1; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23)))) (by exact (Litex.tanhReciprocal ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re)))))
                )
            )
          let _object_w10 := (let _wd_1_0 := (Litex.sech _value_i1 h_23);
          let _wd_1_1 := (Litex.cosh _value_i1 h_23);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.sech _value_i1 h_23)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.sechInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0)))))
          have h_5 : (by
            let _equal_wd_1_0 := _object_w10
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w10;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((Litex.nativeSech ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) * (Real.cosh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _hyp := (_equal_wd_1_0).val.left; Litex.denoteSech _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23)))) (let _hyp := (_equal_wd_1_0).val.right; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by exact (Litex.sechReciprocal ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re)))))
                )
            )
          let _object_w11 := (Litex.tanh _value_i1 h_23)
          let _object_w12 := (let _wd_1_0 := _object_w9;
          let _wd_1_1 := (Litex.sech _value_i1 h_23);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w9
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.sech _value_i1 h_23)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.sechInRPos _atomic_wd_1_0)))))
          have h_6 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w11;
                  let _equal_wd_1_1 := _object_w12;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.tanh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) ((Real.sinh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) * (Litex.nativeSech ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteTanh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23)))) (Litex.NativeBridge.denoteMul (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (let _hyp := _object_w9; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23)))) (let _hyp := (_equal_wd_1_1).val.right; Litex.denoteSech _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23))))) (by exact (Litex.tanhThroughSech ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re)))))
                )
            )
          let _object_w13 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (let _wd_2_0 := _object_w11;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.tanhInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.sub _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (M.real_subset_complex _ (Litex.tanhInR (_atomic_wd_1_0).val.base))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))))
          let _object_w14 := (let _wd_1_0 := (Litex.sech _value_i1 h_23);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (Litex.sech _value_i1 h_23)
            exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.sechInRPos _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          have h_7 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w13;
                  let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((1 : ℂ) - ((Real.tanh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) ^ (2 : ℕ))) ((Litex.nativeSech ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) ^ (2 : ℕ)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_w11
                    exact (Litex.tanhInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _hyp := _object_w11; Litex.denoteTanh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23)))))) (Litex.NativeBridge.denotePowNatReal (_equal_wd_1_1).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (Litex.sech _value_i1 h_23)
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.sechInRPos _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _hyp := (_equal_wd_1_1).val.base; Litex.denoteSech _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23))))) (by exact (Litex.tanhSechSquare ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re)))))
                )
            )
          let _object_w15 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i1 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_23));
          (Litex.sinh _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInR (Litex.number (M := M) (2 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_23))))
          let _object_w16 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_2_1 := _object_w9;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
            let _atomic_wd_1_0 := _object_w9
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))));
          let _wd_1_1 := (Litex.cosh _value_i1 h_23);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.right)))) (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0)))))
          have h_8 : (by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w15;
                  let _equal_wd_1_1 := _object_w16;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.sinh (((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)))).re : ℂ) (((2 : ℂ) * (Real.sinh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ)) * (Real.cosh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteSinh _hyp (((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg ((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))) _hyp.wd (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i1 ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23))))) (Litex.NativeBridge.denoteMul (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_1).val.left).val.right ((_equal_wd_1_1).val.left).wd.1 ((_equal_wd_1_1).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (let _hyp := _object_w9; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23))))) (let _hyp := (_equal_wd_1_1).val.right; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23))))) (by simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]; exact (Litex.sinhDoubleAngle ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re)))))
                )
            )
          let _object_w17 := (let _wd_1_0 := (_object_w15).val.arg;
          (Litex.cosh _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInR (Litex.number (M := M) (2 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_23))))
          let _object_w18 := (let _wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i1 h_23);
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
            exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (let _wd_2_0 := _object_w9;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_w9
            exact (Litex.sinhInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i1 h_23);
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := (Litex.cosh _value_i1 h_23)
              exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.coshInRPos (_atomic_wd_1_0).val.base))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.base))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))))
          have h_9 : (by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w17;
                  let _equal_wd_1_1 := _object_w18;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.cosh (((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)))).re : ℂ) (((Real.cosh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) ^ (2 : ℕ)) + ((Real.sinh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re : ℂ) ^ (2 : ℕ))) (let _hyp := _equal_wd_1_0; Litex.denoteCosh _hyp (((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg ((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))) _hyp.wd (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i1 ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23))))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_1).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (Litex.cosh _value_i1 h_23)
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _hyp := ((_equal_wd_1_1).val.left).val.base; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23))))) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_1).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (Litex.sinhInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _hyp := _object_w9; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_23)))))) (by simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]; exact (Litex.coshDoubleAngle ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_23))).re)))))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 (And.intro h_4 (And.intro h_5 (And.intro h_6 (And.intro h_7 (And.intro h_8 h_9))))))))
        )
      )
  )

theorem h_2335 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_2348 : Litex.In _value_i2 (Litex.R (M := M))) (h_2329 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w21 := (let _wd_1_0 := (Litex.coth _value_i2 h_2348 h_2329);
  let _wd_1_1 := (Litex.sinh _value_i2 h_2348);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.coth _value_i2 h_2348 h_2329)
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cothInRStar _atomic_wd_1_0)))) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_2348)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))))
  let _object_w22 := (Litex.cosh _value_i2 h_2348)
  let _object_w23 := (let _wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329);
  let _wd_1_1 := (Litex.sinh _value_i2 h_2348);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329)
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cschInRStar _atomic_wd_1_0)))) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_2348)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))))
  let _object_w25 := (Litex.coth _value_i2 h_2348 h_2329)
  let _object_w26 := (let _wd_1_0 := _object_w22;
  let _wd_1_1 := (Litex.csch _value_i2 h_2348 h_2329);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _object_w22
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329)
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cschInRStar _atomic_wd_1_0))))))
  let _object_w27 := (let _wd_1_0 := (Litex.tanh _value_i2 h_2348);
  let _wd_1_1 := _object_w25;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.tanh _value_i2 h_2348)
    exact (M.real_subset_complex _ (Litex.tanhInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _object_w25
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cothInRStar _atomic_wd_1_0))))))
  let _object_w28 := (let _wd_1_0 := (let _wd_2_0 := _object_w25;
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _object_w25
    exact (Litex.inRStar_base _atomic_wd_1_0 (Litex.cothInRStar _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (Litex.realToComplex (_atomic_wd_1_0).val.base (Litex.inRStar_base (_atomic_wd_1_0).val.base (Litex.cothInRStar (_atomic_wd_1_0).val.base)))
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    )) (Litex.numberInC (M := M) (1 : ℂ))))
  let _object_w29 := (let _wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329)
    exact (Litex.inRStar_base _atomic_wd_1_0 (Litex.cschInRStar _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
  exact (((by
    let _equal_wd_1_0 := _object_w21
    let _equal_wd_1_1 := _object_w22
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w23
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))) ∧ ((((by
    let _equal_wd_1_0 := _object_w25
    let _equal_wd_1_1 := _object_w26
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w27
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))) ∧ ((by
    let _equal_wd_1_0 := _object_w28
    let _equal_wd_1_1 := _object_w29
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_2348 h_2329
          let _object_w21 := (let _wd_1_0 := (Litex.coth _value_i2 h_2348 h_2329);
          let _wd_1_1 := (Litex.sinh _value_i2 h_2348);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.coth _value_i2 h_2348 h_2329)
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cothInRStar _atomic_wd_1_0)))) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_2348)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))))
          let _object_w22 := (Litex.cosh _value_i2 h_2348)
          have h_2330 : (by
            let _equal_wd_1_0 := _object_w21
            let _equal_wd_1_1 := _object_w22
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w21;
                  let _equal_wd_1_1 := _object_w22;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((Litex.nativeCoth ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ) * (Real.sinh ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ)) (Real.cosh ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _hyp := (_equal_wd_1_0).val.left; Litex.denoteCoth _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348)))) (let _hyp := (_equal_wd_1_0).val.right; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348))))) (let _hyp := _equal_wd_1_1; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348)))) (by have _argument := Litex.NativeBridge.denoteRealOfDenoteNumber ((_equal_wd_1_0).val.left).val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) ((_equal_wd_1_0).val.left).wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348)); have _nonzero : ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re ≠ 0 := fun h => ((_equal_wd_1_0).val.left).wd.2 (_argument.trans (by rw [h]; rfl)); exact (Litex.cothReciprocal ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re _nonzero)))))
                )
            )
          let _object_w23 := (let _wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329);
          let _wd_1_1 := (Litex.sinh _value_i2 h_2348);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329)
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cschInRStar _atomic_wd_1_0)))) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_2348)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))))
          have h_2331 : (by
            let _equal_wd_1_0 := _object_w23
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w23;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((Litex.nativeCsch ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ) * (Real.sinh ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _hyp := (_equal_wd_1_0).val.left; Litex.denoteCsch _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348)))) (let _hyp := (_equal_wd_1_0).val.right; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by have _argument := Litex.NativeBridge.denoteRealOfDenoteNumber ((_equal_wd_1_0).val.left).val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) ((_equal_wd_1_0).val.left).wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348)); have _nonzero : ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re ≠ 0 := fun h => ((_equal_wd_1_0).val.left).wd.2 (_argument.trans (by rw [h]; rfl)); exact (Litex.cschReciprocal ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re _nonzero)))))
                )
            )
          let _object_w25 := (Litex.coth _value_i2 h_2348 h_2329)
          let _object_w26 := (let _wd_1_0 := _object_w22;
          let _wd_1_1 := (Litex.csch _value_i2 h_2348 h_2329);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w22
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329)
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cschInRStar _atomic_wd_1_0))))))
          have h_2332 : (by
            let _equal_wd_1_0 := _object_w25
            let _equal_wd_1_1 := _object_w26
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w25;
                  let _equal_wd_1_1 := _object_w26;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeCoth ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ) ((Real.cosh ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ) * (Litex.nativeCsch ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteCoth _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348)))) (Litex.NativeBridge.denoteMul (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (let _hyp := _object_w22; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348)))) (let _hyp := (_equal_wd_1_1).val.right; Litex.denoteCsch _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348))))) (by exact (Litex.cothThroughCsch ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re)))))
                )
            )
          let _object_w27 := (let _wd_1_0 := (Litex.tanh _value_i2 h_2348);
          let _wd_1_1 := _object_w25;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.tanh _value_i2 h_2348)
            exact (M.real_subset_complex _ (Litex.tanhInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _object_w25
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cothInRStar _atomic_wd_1_0))))))
          have h_2333 : (by
            let _equal_wd_1_0 := _object_w27
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w27;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((Real.tanh ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ) * (Litex.nativeCoth ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _hyp := (_equal_wd_1_0).val.left; Litex.denoteTanh _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348)))) (let _hyp := _object_w25; Litex.denoteCoth _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by have _argument := Litex.NativeBridge.denoteRealOfDenoteNumber ((_equal_wd_1_0).val.right).val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) ((_equal_wd_1_0).val.right).wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348)); have _nonzero : ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re ≠ 0 := fun h => ((_equal_wd_1_0).val.right).wd.2 (_argument.trans (by rw [h]; rfl)); exact (Litex.tanhCothProduct ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re _nonzero)))))
                )
            )
          let _object_w28 := (let _wd_1_0 := (let _wd_2_0 := _object_w25;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_w25
            exact (Litex.inRStar_base _atomic_wd_1_0 (Litex.cothInRStar _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.realToComplex (_atomic_wd_1_0).val.base (Litex.inRStar_base (_atomic_wd_1_0).val.base (Litex.cothInRStar (_atomic_wd_1_0).val.base)))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.numberInC (M := M) (1 : ℂ))))
          let _object_w29 := (let _wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329)
            exact (Litex.inRStar_base _atomic_wd_1_0 (Litex.cschInRStar _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          have h_2334 : (by
            let _equal_wd_1_0 := _object_w28
            let _equal_wd_1_1 := _object_w29
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w28;
                  let _equal_wd_1_1 := _object_w29;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((Litex.nativeCoth ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ) ^ (2 : ℕ)) - (1 : ℂ)) ((Litex.nativeCsch ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re : ℂ) ^ (2 : ℕ)) (Litex.NativeBridge.denoteSub (_equal_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_w25
                    exact (Litex.inRStar_base _atomic_wd_1_0 (Litex.cothInRStar _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _hyp := _object_w25; Litex.denoteCoth _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denotePowNatReal (_equal_wd_1_1).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (Litex.csch _value_i2 h_2348 h_2329)
                    exact (Litex.inRStar_base _atomic_wd_1_0 (Litex.cschInRStar _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _hyp := (_equal_wd_1_1).val.base; Litex.denoteCsch _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348))))) (by have _argument := Litex.NativeBridge.denoteRealOfDenoteNumber (((_equal_wd_1_0).val.left).val.base).val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348)) (((_equal_wd_1_0).val.left).val.base).wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_2348)); have _nonzero : ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re ≠ 0 := fun h => (((_equal_wd_1_0).val.left).val.base).wd.2 (_argument.trans (by rw [h]; rfl)); exact (Litex.cothCschSquare ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_2348))).re _nonzero)))))
                )
            )
          exact (And.intro h_2330 (And.intro h_2331 (And.intro h_2332 (And.intro h_2333 h_2334))))
        )
      )
  )

theorem h_3787 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3800 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_3801 : Litex.In _value_i4 (Litex.R (M := M))), (by
  let _object_w31 := (let _wd_1_0 := (Litex.add _value_i3 _value_i4 (M.real_subset_complex _ h_3800) (M.real_subset_complex _ h_3801));
  (Litex.sinh _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInR _value_i3 _value_i4 h_3800 h_3801))))
  let _object_w32 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sinh _value_i3 h_3800);
  let _wd_2_1 := (Litex.cosh _value_i4 h_3801);
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i3 h_3800)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i4 h_3801)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0)))));
  let _wd_1_1 := (let _wd_2_0 := (Litex.cosh _value_i3 h_3800);
  let _wd_2_1 := (Litex.sinh _value_i4 h_3801);
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i3 h_3800)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i4 h_3801)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.sinh _value_i3 h_3800);
    let _wd_2_1 := (Litex.cosh _value_i4 h_3801);
    (Litex.mul _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := (Litex.sinh _value_i3 h_3800)
      exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_2_0))) (by
      let _atomic_wd_2_0 := (Litex.cosh _value_i4 h_3801)
      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0)))))
    exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.left)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.coshInRPos (_atomic_wd_1_0).val.right)))) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i3 h_3800);
    let _wd_2_1 := (Litex.sinh _value_i4 h_3801);
    (Litex.mul _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := (Litex.cosh _value_i3 h_3800)
      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0))) (by
      let _atomic_wd_2_0 := (Litex.sinh _value_i4 h_3801)
      exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_2_0)))))
    exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex (_atomic_wd_1_0).val.left (Litex.coshInRPos (_atomic_wd_1_0).val.left)) (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.right))))))
  let _object_w33 := (let _wd_1_0 := (_object_w31).val.arg;
  (Litex.cosh _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInR _value_i3 _value_i4 h_3800 h_3801))))
  let _object_w34 := (let _wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i3 h_3800);
  let _wd_2_1 := (Litex.cosh _value_i4 h_3801);
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i3 h_3800)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i4 h_3801)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0)))));
  let _wd_1_1 := (let _wd_2_0 := (Litex.sinh _value_i3 h_3800);
  let _wd_2_1 := (Litex.sinh _value_i4 h_3801);
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i3 h_3800)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i4 h_3801)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i3 h_3800);
    let _wd_2_1 := (Litex.cosh _value_i4 h_3801);
    (Litex.mul _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := (Litex.cosh _value_i3 h_3800)
      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0))) (by
      let _atomic_wd_2_0 := (Litex.cosh _value_i4 h_3801)
      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0)))))
    exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex (_atomic_wd_1_0).val.left (Litex.coshInRPos (_atomic_wd_1_0).val.left)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.coshInRPos (_atomic_wd_1_0).val.right)))) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.sinh _value_i3 h_3800);
    let _wd_2_1 := (Litex.sinh _value_i4 h_3801);
    (Litex.mul _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := (Litex.sinh _value_i3 h_3800)
      exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_2_0))) (by
      let _atomic_wd_2_0 := (Litex.sinh _value_i4 h_3801)
      exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_2_0)))))
    exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.left)) (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.right))))))
  exact (((by
    let _equal_wd_1_0 := _object_w31
    let _equal_wd_1_1 := _object_w32
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w33
    let _equal_wd_1_1 := _object_w34
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_3800 _Host_i4 _rep_i4 _value_i4 h_3801
          let _object_w31 := (let _wd_1_0 := (Litex.add _value_i3 _value_i4 (M.real_subset_complex _ h_3800) (M.real_subset_complex _ h_3801));
          (Litex.sinh _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInR _value_i3 _value_i4 h_3800 h_3801))))
          let _object_w32 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sinh _value_i3 h_3800);
          let _wd_2_1 := (Litex.cosh _value_i4 h_3801);
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i3 h_3800)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i4 h_3801)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0)))));
          let _wd_1_1 := (let _wd_2_0 := (Litex.cosh _value_i3 h_3800);
          let _wd_2_1 := (Litex.sinh _value_i4 h_3801);
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i3 h_3800)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i4 h_3801)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.sinh _value_i3 h_3800);
            let _wd_2_1 := (Litex.cosh _value_i4 h_3801);
            (Litex.mul _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := (Litex.sinh _value_i3 h_3800)
              exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_2_0))) (by
              let _atomic_wd_2_0 := (Litex.cosh _value_i4 h_3801)
              exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0)))))
            exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.left)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.coshInRPos (_atomic_wd_1_0).val.right)))) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i3 h_3800);
            let _wd_2_1 := (Litex.sinh _value_i4 h_3801);
            (Litex.mul _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := (Litex.cosh _value_i3 h_3800)
              exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0))) (by
              let _atomic_wd_2_0 := (Litex.sinh _value_i4 h_3801)
              exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_2_0)))))
            exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex (_atomic_wd_1_0).val.left (Litex.coshInRPos (_atomic_wd_1_0).val.left)) (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.right))))))
          have h_3785 : (by
            let _equal_wd_1_0 := _object_w31
            let _equal_wd_1_1 := _object_w32
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w31;
                  let _equal_wd_1_1 := _object_w32;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.sinh (((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800)) + (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801)))).re : ℂ) (((Real.sinh ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800))).re : ℂ) * (Real.cosh ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))).re : ℂ)) + ((Real.cosh ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800))).re : ℂ) * (Real.sinh ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))).re : ℂ))) (let _hyp := _equal_wd_1_0; Litex.denoteSinh _hyp (((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800)) + (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801)))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800)) + (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))) _hyp.wd (Litex.NativeBridge.denoteAdd _value_i3 _value_i4 ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_3800)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_3801))))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteMul ((_equal_wd_1_1).val.left).val.left ((_equal_wd_1_1).val.left).val.right ((_equal_wd_1_1).val.left).wd.1 ((_equal_wd_1_1).val.left).wd.2 _ _ (let _hyp := ((_equal_wd_1_1).val.left).val.left; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_3800)))) (let _hyp := ((_equal_wd_1_1).val.left).val.right; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_3801))))) (Litex.NativeBridge.denoteMul ((_equal_wd_1_1).val.right).val.left ((_equal_wd_1_1).val.right).val.right ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (let _hyp := ((_equal_wd_1_1).val.right).val.left; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_3800)))) (let _hyp := ((_equal_wd_1_1).val.right).val.right; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_3801)))))) (by simpa only [Complex.add_re] using (Litex.sinhAddition ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800))).re ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))).re)))))
                )
            )
          let _object_w33 := (let _wd_1_0 := (_object_w31).val.arg;
          (Litex.cosh _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInR _value_i3 _value_i4 h_3800 h_3801))))
          let _object_w34 := (let _wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i3 h_3800);
          let _wd_2_1 := (Litex.cosh _value_i4 h_3801);
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i3 h_3800)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i4 h_3801)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0)))));
          let _wd_1_1 := (let _wd_2_0 := (Litex.sinh _value_i3 h_3800);
          let _wd_2_1 := (Litex.sinh _value_i4 h_3801);
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i3 h_3800)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i4 h_3801)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.cosh _value_i3 h_3800);
            let _wd_2_1 := (Litex.cosh _value_i4 h_3801);
            (Litex.mul _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := (Litex.cosh _value_i3 h_3800)
              exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0))) (by
              let _atomic_wd_2_0 := (Litex.cosh _value_i4 h_3801)
              exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0)))))
            exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex (_atomic_wd_1_0).val.left (Litex.coshInRPos (_atomic_wd_1_0).val.left)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.coshInRPos (_atomic_wd_1_0).val.right)))) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.sinh _value_i3 h_3800);
            let _wd_2_1 := (Litex.sinh _value_i4 h_3801);
            (Litex.mul _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := (Litex.sinh _value_i3 h_3800)
              exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_2_0))) (by
              let _atomic_wd_2_0 := (Litex.sinh _value_i4 h_3801)
              exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_2_0)))))
            exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.left)) (M.real_subset_complex _ (Litex.sinhInR (_atomic_wd_1_0).val.right))))))
          have h_3786 : (by
            let _equal_wd_1_0 := _object_w33
            let _equal_wd_1_1 := _object_w34
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w33;
                  let _equal_wd_1_1 := _object_w34;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.cosh (((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800)) + (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801)))).re : ℂ) (((Real.cosh ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800))).re : ℂ) * (Real.cosh ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))).re : ℂ)) + ((Real.sinh ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800))).re : ℂ) * (Real.sinh ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))).re : ℂ))) (let _hyp := _equal_wd_1_0; Litex.denoteCosh _hyp (((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800)) + (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801)))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800)) + (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))) _hyp.wd (Litex.NativeBridge.denoteAdd _value_i3 _value_i4 ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_3800)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_3801))))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteMul ((_equal_wd_1_1).val.left).val.left ((_equal_wd_1_1).val.left).val.right ((_equal_wd_1_1).val.left).wd.1 ((_equal_wd_1_1).val.left).wd.2 _ _ (let _hyp := ((_equal_wd_1_1).val.left).val.left; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_3800)))) (let _hyp := ((_equal_wd_1_1).val.left).val.right; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_3801))))) (Litex.NativeBridge.denoteMul ((_equal_wd_1_1).val.right).val.left ((_equal_wd_1_1).val.right).val.right ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (let _hyp := ((_equal_wd_1_1).val.right).val.left; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_3800)))) (let _hyp := ((_equal_wd_1_1).val.right).val.right; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_3801)))))) (by simpa only [Complex.add_re] using (Litex.coshAddition ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_3800))).re ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_3801))).re)))))
                )
            )
          exact (And.intro h_3785 h_3786)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_identities_x2f_statement_x2e_lit

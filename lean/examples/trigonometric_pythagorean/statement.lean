import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_trigonometric_x5f_pythagorean_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sin _value_i1 h_15);
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := (Litex.sin _value_i1 h_15)
    exact (Litex.sinInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  let _wd_1_1 := (let _wd_2_0 := (Litex.cos _value_i1 h_15);
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := (Litex.cos _value_i1 h_15)
    exact (Litex.cosInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.sin _value_i1 h_15);
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_2_0 := (Litex.sin _value_i1 h_15)
      exact (Litex.sinInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (M.real_subset_complex _ (Litex.sinInR (_atomic_wd_1_0).val.base))
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    )) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.cos _value_i1 h_15);
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_2_0 := (Litex.cos _value_i1 h_15)
      exact (Litex.cosInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (M.real_subset_complex _ (Litex.cosInR (_atomic_wd_1_0).val.base))
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))))
  exact (by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          let _object_w2 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sin _value_i1 h_15);
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (Litex.sin _value_i1 h_15)
            exact (Litex.sinInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (let _wd_2_0 := (Litex.cos _value_i1 h_15);
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (Litex.cos _value_i1 h_15)
            exact (Litex.cosInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.sin _value_i1 h_15);
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := (Litex.sin _value_i1 h_15)
              exact (Litex.sinInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (M.real_subset_complex _ (Litex.sinInR (_atomic_wd_1_0).val.base))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.cos _value_i1 h_15);
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := (Litex.cos _value_i1 h_15)
              exact (Litex.cosInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (M.real_subset_complex _ (Litex.cosInR (_atomic_wd_1_0).val.base))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (((Real.sin ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_15))).re : ℂ) ^ (2 : ℕ)) + ((Real.cos ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_15))).re : ℂ) ^ (2 : ℕ))) (1 : ℂ) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (Litex.sin _value_i1 h_15)
                    exact (Litex.sinInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _trig := ((_equal_wd_1_0).val.left).val.base; Litex.denoteSin _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_15))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_15)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_15))))) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (Litex.cos _value_i1 h_15)
                    exact (Litex.cosInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _trig := ((_equal_wd_1_0).val.right).val.base; Litex.denoteCos _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_15))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_15)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_15)))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by simpa only [add_comm] using (Litex.sinSqAddCosSq ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_15))).re)))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_trigonometric_x5f_pythagorean_x2f_statement_x2e_lit

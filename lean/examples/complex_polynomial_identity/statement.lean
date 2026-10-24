import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_polynomial_x5f_identity_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) Complex.I) h_15 (Litex.numberInC (M := M) Complex.I));
  let _wd_1_1 := (Litex.sub _value_i1 (Litex.number (M := M) Complex.I) h_15 (Litex.numberInC (M := M) Complex.I));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC _value_i1 (Litex.number (M := M) Complex.I) h_15 (Litex.numberInC (M := M) Complex.I))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.subInC _value_i1 (Litex.number (M := M) Complex.I) h_15 (Litex.numberInC (M := M) Complex.I)))))
  let _object_w3 := (let _wd_1_0 := (Litex.powNat _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_15 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := h_15
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    )) (Litex.numberInC (M := M) (1 : ℂ))))
  exact (by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          let _object_w2 := (let _wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) Complex.I) h_15 (Litex.numberInC (M := M) Complex.I));
          let _wd_1_1 := (Litex.sub _value_i1 (Litex.number (M := M) Complex.I) h_15 (Litex.numberInC (M := M) Complex.I));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i1 (Litex.number (M := M) Complex.I) h_15 (Litex.numberInC (M := M) Complex.I))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.subInC _value_i1 (Litex.number (M := M) Complex.I) h_15 (Litex.numberInC (M := M) Complex.I)))))
          let _object_w3 := (let _wd_1_0 := (Litex.powNat _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_15 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := h_15
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.numberInC (M := M) (1 : ℂ))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  let _equal_wd_1_1 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 h_15) + Complex.I) * ((Litex.NativeBridge.asComplex _value_i1 h_15) - Complex.I)) (((Litex.NativeBridge.asComplex _value_i1 h_15) ^ (2 : ℕ)) + (1 : ℂ)) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) Complex.I) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (Litex.NativeBridge.denoteNumber (M := M) Complex.I)) (Litex.NativeBridge.denoteSub _value_i1 (Litex.number (M := M) Complex.I) ((_equal_wd_1_0).val.right).wd.1 ((_equal_wd_1_0).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denotePowNat _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_15 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by litex_normalize_complex))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_polynomial_x5f_identity_x2f_statement_x2e_lit

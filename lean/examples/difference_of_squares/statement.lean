import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_difference_x5f_of_x5f_squares_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_1_1 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.addInC _value_i1 (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i1 (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.numberInC (M := M) (1 : ℂ)))))
  let _object_w3 := (let _wd_1_0 := (Litex.powNat _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_15 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _litex_power := _wd_1_0
    have _elaborated_power_base := h_15
    have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
    exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
  ) (Litex.numberInC (M := M) (1 : ℂ))))
  exact Litex.Same _object_w2 _object_w3
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_15
    let _object_w2 := (let _wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_1 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.addInC _value_i1 (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i1 (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.numberInC (M := M) (1 : ℂ)))))
    let _object_w3 := (let _wd_1_0 := (Litex.powNat _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_15 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _litex_power := _wd_1_0
      have _elaborated_power_base := h_15
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ) (Litex.numberInC (M := M) (1 : ℂ))))
    have h_1 : Litex.Same _object_w2 _object_w3 :=
      (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 h_15) + (1 : ℂ)) * ((Litex.NativeBridge.asComplex _value_i1 h_15) - (1 : ℂ))) (((Litex.NativeBridge.asComplex _value_i1 h_15) ^ (2 : ℕ)) - (1 : ℂ)) (Litex.NativeBridge.denoteMul (_object_w2).val.left (_object_w2).val.right (_object_w2).wd.1 (_object_w2).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (1 : ℂ)) ((_object_w2).val.left).wd.1 ((_object_w2).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i1 (Litex.number (M := M) (1 : ℂ)) ((_object_w2).val.right).wd.1 ((_object_w2).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteSub (_object_w3).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w3).wd.1 (_object_w3).wd.2 _ _ (Litex.NativeBridge.denotePowNat _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_15 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by ring))
    exact h_1
  )
end LitexCompiled.file_lean_x2f_examples_x2f_difference_x5f_of_x5f_squares_x2f_statement_x2e_lit

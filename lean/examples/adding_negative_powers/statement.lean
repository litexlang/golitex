import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_adding_x5f_negative_x5f_powers_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.C (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w3 := (let _wd_1_0 := (let _wd_2_0 := _value_i1;
  let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
  (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))));
  let _wd_1_1 := (let _wd_2_0 := _value_i1;
  let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
  (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := _value_i1;
    let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
    (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
      let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := h_16
      have _elaborated_power_exponent := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.exponent (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    )) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := _value_i1;
    let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
    (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
      let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := h_16
      have _elaborated_power_exponent := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.exponent (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))))
  let _object_w4 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_1 := (let _wd_2_0 := _value_i1;
  let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
  (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))));
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := _value_i1;
    let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
    (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
      let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := h_16
      have _elaborated_power_exponent := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.exponent (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))))
  exact Litex.Same _object_w3 _object_w4
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
    let _object_w3 := (let _wd_1_0 := (let _wd_2_0 := _value_i1;
    let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
    (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
      let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))));
    let _wd_1_1 := (let _wd_2_0 := _value_i1;
    let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
    (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
      let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (let _wd_2_0 := _value_i1;
      let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
      (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))))
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := h_16
        have _elaborated_power_exponent := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.exponent (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (by
      let _atomic_wd_1_0 := (let _wd_2_0 := _value_i1;
      let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
      (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))))
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := h_16
        have _elaborated_power_exponent := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.exponent (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))))
    let _object_w4 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_1 := (let _wd_2_0 := _value_i1;
    let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
    (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
      let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))));
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
      let _atomic_wd_1_0 := (let _wd_2_0 := _value_i1;
      let _wd_2_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
      (Litex.powInt _wd_2_0 _wd_2_1 (-2 : ℤ) h_16 (by
        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num))))
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := h_16
        have _elaborated_power_exponent := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.exponent (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))))
    have h_2 : Litex.Same _object_w3 _object_w4 :=
      (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 h_16) ^ (-2 : ℤ)) + ((Litex.NativeBridge.asComplex _value_i1 h_16) ^ (-2 : ℤ))) ((2 : ℂ) * ((Litex.NativeBridge.asComplex _value_i1 h_16) ^ (-2 : ℤ))) (Litex.NativeBridge.denoteAdd (_object_w3).val.left (_object_w3).val.right (_object_w3).wd.1 (_object_w3).wd.2 _ _ (Litex.NativeBridge.denotePowInt _value_i1 ((_object_w3).val.left).val.exponent (-2 : ℤ) h_16 (by
        let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber ((_object_w3).val.left).val.exponent (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (((_object_w3).val.left).val.exponent).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 h_16)) (Litex.NativeBridge.denotePowInt _value_i1 ((_object_w3).val.right).val.exponent (-2 : ℤ) h_16 (by
        let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber ((_object_w3).val.right).val.exponent (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (((_object_w3).val.right).val.exponent).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 h_16))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (_object_w4).val.right (_object_w4).wd.1 (_object_w4).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denotePowInt _value_i1 ((_object_w4).val.right).val.exponent (-2 : ℤ) h_16 (by
        let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) h_1 (Litex.NativeBridge.sameOfDenoteNumber ((_object_w4).val.right).val.exponent (Litex.number (M := M) ((-2 : ℤ) : ℂ)) (- (2 : ℂ)) ((-2 : ℤ) : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (((_object_w4).val.right).val.exponent).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((-2 : ℤ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 h_16))) (by
        have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i1 h_16) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 h_16) (Litex.NativeBridge.asComplex_spec _value_i1 h_16) h_1
        litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
      ))
    exact h_2
  )
end LitexCompiled.file_lean_x2f_examples_x2f_adding_x5f_negative_x5f_powers_x2f_statement_x2e_lit

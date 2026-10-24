import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_triple_x5f_product_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_10 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_33 : Litex.In _value_i3 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(let _setElement_0 := _wd_1_0;
  let _setElement_1 := _wd_1_1;
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0))), (by
  have h_7 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_6).1
        )
    )
  have h_11 : Litex.In _value_i2 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_10).1
        )
    )
  exact Litex.Same (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_7) (Litex.integerToComplex _value_i2 h_11));
  let _wd_1_1 := _value_i3;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_7) (Litex.integerToComplex _value_i2 h_11))) (by
    have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
      let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
    have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
    have _finite_source : M.mem (Litex.denote _wd_1_1) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
      let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
      (let _setElement_0 := _wd_1_0;
        let _setElement_1 := _wd_1_1;
        let _setTail_2 := Litex.emptySet (M := M);
        let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
        let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0))
      exact h_33)
    exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _wd_1_1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _wd_1_1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _wd_1_1) _finite_tail))))))
  ))) (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.mul _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_11) (by
    have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
      let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
    have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
    have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
      let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
      (let _setElement_0 := _wd_1_0;
        let _setElement_1 := _wd_1_1;
        let _setTail_2 := Litex.emptySet (M := M);
        let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
        let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0))
      exact h_33)
    exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
  ));
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.integerToComplex _wd_1_0 h_7) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_10 _Host_i3 _rep_i3 _value_i3 h_33
          have h_7 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_6).1
                )
            )
          have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_6).2.1
                )
            )
          have h_9 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_6).2.2
                )
            )
          have h_11 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_10).1
                )
            )
          have h_12 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_10).2.1
                )
            )
          have h_13 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_10).2.2
                )
            )
          change ((M.mulValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote _value_i1) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))
          exact (by
            obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_6
            have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
            rcases _enumerated_values with _enumerated_value | _enumerated_value
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
              exact (by
                obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_10
                have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                rcases _enumerated_values with _enumerated_value | _enumerated_value
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp h_33) (fun _enumerated_case_2 => (by
                    have h_4049 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_4050 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_4049).1
                          )
                      )
                    have h_4051 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_4049).2.1
                          )
                      )
                    have h_4052 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_4049).2.2
                          )
                      )
                    have h_4053 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_10
                          )
                      )
                    have h_4054 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_4053).1
                          )
                      )
                    have h_4055 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_4053).2.1
                          )
                      )
                    have h_4056 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_4053).2.2
                          )
                      )
                    have h_4076 : Litex.In _value_i3 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (let _setElement_0 := _wd_1_0;
                      let _setElement_1 := _wd_1_1;
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_33
                          )
                      )
                    have h_4080 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_4081 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_4082 : Litex.Same _value_i3 (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_2
                          )
                      )
                    let _object_w12 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_4050) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_4080).trans (h_4081).symm) (show @Eq M.Value _ _ from Eq.refl _) h_4050)));
                    let _wd_1_1 := _value_i3;
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_4050) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_4080).trans (h_4081).symm) (show @Eq M.Value _ _ from Eq.refl _) h_4050)))) (by
                      have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _wd_1_1) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (let _setElement_0 := _wd_1_0;
                          let _setElement_1 := _wd_1_1;
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                            let _atomic_wd_1_0 := _wd_1_0
                            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0))
                        exact h_4076)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _wd_1_1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _wd_1_1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _wd_1_1) _finite_tail))))))
                    )))

                    let _object_w13 := (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i3 (Litex.integerToComplex _value_i2 (Litex.inOfSame _wd_1_0 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_4080).trans (h_4081).symm) (show @Eq M.Value _ _ from Eq.refl _) h_4050)) (by
                      have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (let _setElement_0 := _wd_1_0;
                          let _setElement_1 := _wd_1_1;
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                            let _atomic_wd_1_0 := _wd_1_0
                            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0))
                        exact h_4076)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                    ));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.integerToComplex _wd_1_0 h_4050) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2))))

                    have h_3 : (by
                      let _equal_wd_1_0 := _object_w12
                      let _equal_wd_1_1 := _object_w13
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w12;
                            let _equal_wd_1_1 := _object_w13;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_4050)) * (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_4080).trans (h_4081).symm) (show @Eq M.Value _ _ from Eq.refl _) h_4050)))) * (Litex.NativeBridge.asComplex _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_4076)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            ))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_4050)) * ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_4080).trans (h_4081).symm) (show @Eq M.Value _ _ from Eq.refl _) h_4050))) * (Litex.NativeBridge.asComplex _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_4076)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            )))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i1 _value_i2 ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_4050)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_4080).trans (h_4081).symm) (show @Eq M.Value _ _ from Eq.refl _) h_4050)))) (Litex.NativeBridge.asComplex_spec _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_4076)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            ))) (Litex.NativeBridge.denoteMul _value_i1 (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_4050)) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_4080).trans (h_4081).symm) (show @Eq M.Value _ _ from Eq.refl _) h_4050))) (Litex.NativeBridge.asComplex_spec _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_4076)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            )))) (by ring!))))
                          )
                      )
                    have h_8285 : (by
                      let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                      let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      (Litex.mul _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))))
                      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
                      let _wd_1_1 := (let _wd_2_0 := (Litex.number (M := M) (0 : ℂ));
                      let _wd_2_1 := (_equal_wd_1_0).val.right;
                      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_2_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (- (1 : ℂ))) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                            let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            (Litex.mul _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
                            let _wd_1_1 := (let _wd_2_0 := (Litex.number (M := M) (0 : ℂ));
                            let _wd_2_1 := (_equal_wd_1_0).val.right;
                            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_2_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (- (1 : ℂ))) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))));
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((0 : ℂ) * (0 : ℂ)) * (- (1 : ℂ))) ((0 : ℂ) * ((0 : ℂ) * (- (1 : ℂ)))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) ((_equal_wd_1_1).val.right).val.right ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))) (by norm_num))))
                          )
                      )
                    show ((M.mulValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote _value_i1) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))
                    exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue _enumeration_value (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (0 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue _enumeration_value (Litex.denote _value_i3))))) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) _enumeration_value) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue (M.number (0 : ℂ)) _enumeration_value)))) _enumerated_case_2)) (show ((M.mulValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.negValue (M.number (1 : ℂ)))) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue (M.number (0 : ℂ)) (M.negValue (M.number (1 : ℂ)))))) from h_8285)
                  )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _enumerated_tail) (fun _enumerated_case_2 => (by
                    have h_8483 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_8484 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_8483).1
                          )
                      )
                    have h_8485 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_8483).2.1
                          )
                      )
                    have h_8486 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_8483).2.2
                          )
                      )
                    have h_8487 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_10
                          )
                      )
                    have h_8488 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_8487).1
                          )
                      )
                    have h_8489 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_8487).2.1
                          )
                      )
                    have h_8490 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_8487).2.2
                          )
                      )
                    have h_8510 : Litex.In _value_i3 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (let _setElement_0 := _wd_1_0;
                      let _setElement_1 := _wd_1_1;
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_33
                          )
                      )
                    have h_8514 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_8515 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_8516 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_2
                          )
                      )
                    let _object_w22 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_8484) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_8514).trans (h_8515).symm) (show @Eq M.Value _ _ from Eq.refl _) h_8484)));
                    let _wd_1_1 := _value_i3;
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_8484) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_8514).trans (h_8515).symm) (show @Eq M.Value _ _ from Eq.refl _) h_8484)))) (by
                      have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _wd_1_1) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (let _setElement_0 := _wd_1_0;
                          let _setElement_1 := _wd_1_1;
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                            let _atomic_wd_1_0 := _wd_1_0
                            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0))
                        exact h_8510)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _wd_1_1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _wd_1_1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _wd_1_1) _finite_tail))))))
                    )))

                    let _object_w23 := (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i3 (Litex.integerToComplex _value_i2 (Litex.inOfSame _wd_1_0 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_8514).trans (h_8515).symm) (show @Eq M.Value _ _ from Eq.refl _) h_8484)) (by
                      have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (let _setElement_0 := _wd_1_0;
                          let _setElement_1 := _wd_1_1;
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                            let _atomic_wd_1_0 := _wd_1_0
                            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0))
                        exact h_8510)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                    ));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.integerToComplex _wd_1_0 h_8484) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2))))

                    have h_3 : (by
                      let _equal_wd_1_0 := _object_w22
                      let _equal_wd_1_1 := _object_w23
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w22;
                            let _equal_wd_1_1 := _object_w23;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_8484)) * (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_8514).trans (h_8515).symm) (show @Eq M.Value _ _ from Eq.refl _) h_8484)))) * (Litex.NativeBridge.asComplex _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_8510)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            ))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_8484)) * ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_8514).trans (h_8515).symm) (show @Eq M.Value _ _ from Eq.refl _) h_8484))) * (Litex.NativeBridge.asComplex _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_8510)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            )))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i1 _value_i2 ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_8484)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_8514).trans (h_8515).symm) (show @Eq M.Value _ _ from Eq.refl _) h_8484)))) (Litex.NativeBridge.asComplex_spec _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_8510)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            ))) (Litex.NativeBridge.denoteMul _value_i1 (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_8484)) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_8514).trans (h_8515).symm) (show @Eq M.Value _ _ from Eq.refl _) h_8484))) (Litex.NativeBridge.asComplex_spec _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_8510)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            )))) (by ring!))))
                          )
                      )
                    have h_12747 : (by
                      let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                      (Litex.mul _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
                      let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (1 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.mul _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))));
                            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
                            let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (1 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))));
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((0 : ℂ) * (0 : ℂ)) * (1 : ℂ)) ((0 : ℂ) * ((0 : ℂ) * (1 : ℂ))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (by norm_num))))
                          )
                      )
                    show ((M.mulValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote _value_i1) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))
                    exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue _enumeration_value (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (0 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue _enumeration_value (Litex.denote _value_i3))))) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) _enumeration_value) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue (M.number (0 : ℂ)) _enumeration_value)))) _enumerated_case_2)) (show ((M.mulValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.number (1 : ℂ))) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue (M.number (0 : ℂ)) (M.number (1 : ℂ))))) from h_12747)
                  )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _enumerated_tail))))))
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp h_33) (fun _enumerated_case_2 => (by
                    have h_12945 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_12946 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_12945).1
                          )
                      )
                    have h_12947 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_12945).2.1
                          )
                      )
                    have h_12948 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_12945).2.2
                          )
                      )
                    have h_12949 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_10
                          )
                      )
                    have h_12950 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_12949).1
                          )
                      )
                    have h_12951 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_12949).2.1
                          )
                      )
                    have h_12952 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_12949).2.2
                          )
                      )
                    have h_12972 : Litex.In _value_i3 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (let _setElement_0 := _wd_1_0;
                      let _setElement_1 := _wd_1_1;
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_33
                          )
                      )
                    have h_12976 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_12977 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_12978 : Litex.Same _value_i3 (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_2
                          )
                      )
                    let _object_w33 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_12946) (Litex.integerToComplex _value_i2 h_12950));
                    let _wd_1_1 := _value_i3;
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_12946) (Litex.integerToComplex _value_i2 h_12950))) (by
                      have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _wd_1_1) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (let _setElement_0 := _wd_1_0;
                          let _setElement_1 := _wd_1_1;
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                            let _atomic_wd_1_0 := _wd_1_0
                            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0))
                        exact h_12972)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _wd_1_1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _wd_1_1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _wd_1_1) _finite_tail))))))
                    )))

                    let _object_w34 := (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12950) (by
                      have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (let _setElement_0 := _wd_1_0;
                          let _setElement_1 := _wd_1_1;
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                            let _atomic_wd_1_0 := _wd_1_0
                            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0))
                        exact h_12972)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                    ));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.integerToComplex _wd_1_0 h_12946) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2))))

                    have h_3 : (by
                      let _equal_wd_1_0 := _object_w33
                      let _equal_wd_1_1 := _object_w34
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w33;
                            let _equal_wd_1_1 := _object_w34;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_12946)) * (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_12950))) * (Litex.NativeBridge.asComplex _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_12972)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            ))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_12946)) * ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_12950)) * (Litex.NativeBridge.asComplex _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_12972)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            )))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i1 _value_i2 ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_12946)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_12950))) (Litex.NativeBridge.asComplex_spec _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_12972)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            ))) (Litex.NativeBridge.denoteMul _value_i1 (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_12946)) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_12950)) (Litex.NativeBridge.asComplex_spec _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_12972)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            )))) (by ring!))))
                          )
                      )
                    have h_17086 : (by
                      let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      (Litex.mul _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (1 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))))
                      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
                      let _wd_1_1 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
                      let _wd_2_1 := (_equal_wd_1_0).val.right;
                      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_2_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (- (1 : ℂ))) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))))
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            (Litex.mul _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (1 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
                            let _wd_1_1 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
                            let _wd_2_1 := (_equal_wd_1_0).val.right;
                            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_2_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (- (1 : ℂ))) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((0 : ℂ) * (1 : ℂ)) * (- (1 : ℂ))) ((0 : ℂ) * ((1 : ℂ) * (- (1 : ℂ)))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_1).val.right).val.right ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))) (by norm_num))))
                          )
                      )
                    show ((M.mulValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote _value_i1) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))
                    exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue _enumeration_value (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (0 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue _enumeration_value (Litex.denote _value_i3))))) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) _enumeration_value) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue (M.number (1 : ℂ)) _enumeration_value)))) _enumerated_case_2)) (show ((M.mulValue (M.mulValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) (M.negValue (M.number (1 : ℂ)))) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue (M.number (1 : ℂ)) (M.negValue (M.number (1 : ℂ)))))) from h_17086)
                  )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _enumerated_tail) (fun _enumerated_case_2 => (by
                    have h_17256 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_17257 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_17256).1
                          )
                      )
                    have h_17258 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_17256).2.1
                          )
                      )
                    have h_17259 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_17256).2.2
                          )
                      )
                    have h_17260 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_10
                          )
                      )
                    have h_17261 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_17260).1
                          )
                      )
                    have h_17262 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_17260).2.1
                          )
                      )
                    have h_17263 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_17260).2.2
                          )
                      )
                    have h_17283 : Litex.In _value_i3 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (let _setElement_0 := _wd_1_0;
                      let _setElement_1 := _wd_1_1;
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_33
                          )
                      )
                    have h_17287 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_17288 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_17289 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_2
                          )
                      )
                    let _object_w43 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_17257) (Litex.integerToComplex _value_i2 h_17261));
                    let _wd_1_1 := _value_i3;
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_17257) (Litex.integerToComplex _value_i2 h_17261))) (Litex.integerToComplex _wd_1_1 (Litex.inOfSame _value_i2 _wd_1_1 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_17288).trans (h_17289).symm) (show @Eq M.Value _ _ from Eq.refl _) h_17261))))

                    let _object_w44 := (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_17261) (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i2 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_17288).trans (h_17289).symm) (show @Eq M.Value _ _ from Eq.refl _) h_17261)));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.integerToComplex _wd_1_0 h_17257) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_17261) (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i2 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_17288).trans (h_17289).symm) (show @Eq M.Value _ _ from Eq.refl _) h_17261))))))

                    have h_3 : (by
                      let _equal_wd_1_0 := _object_w43
                      let _equal_wd_1_1 := _object_w44
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w43;
                            let _equal_wd_1_1 := _object_w44;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_17257)) * (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_17261))) * (Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i2 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_17288).trans (h_17289).symm) (show @Eq M.Value _ _ from Eq.refl _) h_17261)))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_17257)) * ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_17261)) * (Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i2 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_17288).trans (h_17289).symm) (show @Eq M.Value _ _ from Eq.refl _) h_17261))))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i1 _value_i2 ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_17257)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_17261))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i2 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_17288).trans (h_17289).symm) (show @Eq M.Value _ _ from Eq.refl _) h_17261)))) (Litex.NativeBridge.denoteMul _value_i1 (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_17257)) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_17261)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i2 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_17288).trans (h_17289).symm) (show @Eq M.Value _ _ from Eq.refl _) h_17261))))) (by ring!))))
                          )
                      )
                    have h_18047 : (by
                      let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                      (Litex.mul _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (1 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
                      let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.mul _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (1 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))));
                            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
                            let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))));
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((0 : ℂ) * (1 : ℂ)) * (1 : ℂ)) ((0 : ℂ) * ((1 : ℂ) * (1 : ℂ))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (by norm_num))))
                          )
                      )
                    show ((M.mulValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote _value_i1) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))
                    exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue _enumeration_value (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (0 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue _enumeration_value (Litex.denote _value_i3))))) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) _enumeration_value) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue (M.number (1 : ℂ)) _enumeration_value)))) _enumerated_case_2)) (show ((M.mulValue (M.mulValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) (M.number (1 : ℂ))) = (M.mulValue (M.number (0 : ℂ)) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))))) from h_18047)
                  )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _enumerated_tail))))))
              )
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
              exact (by
                obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_10
                have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                rcases _enumerated_values with _enumerated_value | _enumerated_value
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp h_33) (fun _enumerated_case_2 => (by
                    have h_18237 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_18238 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_18237).1
                          )
                      )
                    have h_18239 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_18237).2.1
                          )
                      )
                    have h_18240 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_18237).2.2
                          )
                      )
                    have h_18241 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_10
                          )
                      )
                    have h_18242 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_18241).1
                          )
                      )
                    have h_18243 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_18241).2.1
                          )
                      )
                    have h_18244 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_18241).2.2
                          )
                      )
                    have h_18264 : Litex.In _value_i3 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (let _setElement_0 := _wd_1_0;
                      let _setElement_1 := _wd_1_1;
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_33
                          )
                      )
                    have h_18268 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_18269 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_18270 : Litex.Same _value_i3 (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_2
                          )
                      )
                    let _object_w54 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_18238) (Litex.integerToComplex _value_i2 h_18242));
                    let _wd_1_1 := _value_i3;
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_18238) (Litex.integerToComplex _value_i2 h_18242))) (by
                      have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _wd_1_1) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (let _setElement_0 := _wd_1_0;
                          let _setElement_1 := _wd_1_1;
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                            let _atomic_wd_1_0 := _wd_1_0
                            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0))
                        exact h_18264)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _wd_1_1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _wd_1_1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _wd_1_1) _finite_tail))))))
                    )))

                    let _object_w55 := (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_18242) (by
                      have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (let _setElement_0 := _wd_1_0;
                          let _setElement_1 := _wd_1_1;
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                            let _atomic_wd_1_0 := _wd_1_0
                            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0))
                        exact h_18264)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                    ));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.integerToComplex _wd_1_0 h_18238) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2))))

                    have h_3 : (by
                      let _equal_wd_1_0 := _object_w54
                      let _equal_wd_1_1 := _object_w55
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w54;
                            let _equal_wd_1_1 := _object_w55;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_18238)) * (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_18242))) * (Litex.NativeBridge.asComplex _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_18264)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            ))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_18238)) * ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_18242)) * (Litex.NativeBridge.asComplex _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_18264)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            )))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i1 _value_i2 ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_18238)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_18242))) (Litex.NativeBridge.asComplex_spec _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_18264)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            ))) (Litex.NativeBridge.denoteMul _value_i1 (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_18238)) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_18242)) (Litex.NativeBridge.asComplex_spec _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_18264)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            )))) (by ring!))))
                          )
                      )
                    have h_22378 : (by
                      let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                      let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      (Litex.mul _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))))
                      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
                      let _wd_1_1 := (let _wd_2_0 := (Litex.number (M := M) (0 : ℂ));
                      let _wd_2_1 := (_equal_wd_1_0).val.right;
                      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_2_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (- (1 : ℂ))) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                            let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            (Litex.mul _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
                            let _wd_1_1 := (let _wd_2_0 := (Litex.number (M := M) (0 : ℂ));
                            let _wd_2_1 := (_equal_wd_1_0).val.right;
                            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_2_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (- (1 : ℂ))) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))));
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((1 : ℂ) * (0 : ℂ)) * (- (1 : ℂ))) ((1 : ℂ) * ((0 : ℂ) * (- (1 : ℂ)))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) ((_equal_wd_1_1).val.right).val.right ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))) (by norm_num))))
                          )
                      )
                    show ((M.mulValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote _value_i1) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))
                    exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue _enumeration_value (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (1 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue _enumeration_value (Litex.denote _value_i3))))) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (1 : ℂ)) (M.number (0 : ℂ))) _enumeration_value) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue (M.number (0 : ℂ)) _enumeration_value)))) _enumerated_case_2)) (show ((M.mulValue (M.mulValue (M.number (1 : ℂ)) (M.number (0 : ℂ))) (M.negValue (M.number (1 : ℂ)))) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue (M.number (0 : ℂ)) (M.negValue (M.number (1 : ℂ)))))) from h_22378)
                  )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _enumerated_tail) (fun _enumerated_case_2 => (by
                    have h_22548 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_22549 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_22548).1
                          )
                      )
                    have h_22550 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_22548).2.1
                          )
                      )
                    have h_22551 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_22548).2.2
                          )
                      )
                    have h_22552 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_10
                          )
                      )
                    have h_22553 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_22552).1
                          )
                      )
                    have h_22554 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_22552).2.1
                          )
                      )
                    have h_22555 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_22552).2.2
                          )
                      )
                    have h_22575 : Litex.In _value_i3 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (let _setElement_0 := _wd_1_0;
                      let _setElement_1 := _wd_1_1;
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_33
                          )
                      )
                    have h_22579 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_22580 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_22581 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_2
                          )
                      )
                    let _object_w64 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_22549) (Litex.integerToComplex _value_i2 h_22553));
                    let _wd_1_1 := _value_i3;
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_22549) (Litex.integerToComplex _value_i2 h_22553))) (Litex.integerToComplex _wd_1_1 (Litex.inOfSame _value_i1 _wd_1_1 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_22579).trans (h_22581).symm) (show @Eq M.Value _ _ from Eq.refl _) h_22549))))

                    let _object_w65 := (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_22553) (Litex.integerToComplex _value_i3 (Litex.inOfSame _wd_1_0 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_22579).trans (h_22581).symm) (show @Eq M.Value _ _ from Eq.refl _) h_22549)));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.integerToComplex _wd_1_0 h_22549) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_22553) (Litex.integerToComplex _value_i3 (Litex.inOfSame _wd_1_0 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_22579).trans (h_22581).symm) (show @Eq M.Value _ _ from Eq.refl _) h_22549))))))

                    have h_3 : (by
                      let _equal_wd_1_0 := _object_w64
                      let _equal_wd_1_1 := _object_w65
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w64;
                            let _equal_wd_1_1 := _object_w65;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_22549)) * (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_22553))) * (Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i1 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_22579).trans (h_22581).symm) (show @Eq M.Value _ _ from Eq.refl _) h_22549)))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_22549)) * ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_22553)) * (Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i1 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_22579).trans (h_22581).symm) (show @Eq M.Value _ _ from Eq.refl _) h_22549))))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i1 _value_i2 ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_22549)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_22553))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i1 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_22579).trans (h_22581).symm) (show @Eq M.Value _ _ from Eq.refl _) h_22549)))) (Litex.NativeBridge.denoteMul _value_i1 (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_22549)) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_22553)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i1 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_22579).trans (h_22581).symm) (show @Eq M.Value _ _ from Eq.refl _) h_22549))))) (by ring!))))
                          )
                      )
                    have h_23331 : (by
                      let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                      (Litex.mul _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
                      let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (1 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.mul _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))));
                            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
                            let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (1 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))));
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((1 : ℂ) * (0 : ℂ)) * (1 : ℂ)) ((1 : ℂ) * ((0 : ℂ) * (1 : ℂ))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (by norm_num))))
                          )
                      )
                    have h_23621 : Litex.Same (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.mulCancelRightLeft (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                              let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                              let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (1 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_23331)
                          )
                      )
                    show ((M.mulValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote _value_i1) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))
                    exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue _enumeration_value (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (1 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue _enumeration_value (Litex.denote _value_i3))))) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (1 : ℂ)) (M.number (0 : ℂ))) _enumeration_value) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue (M.number (0 : ℂ)) _enumeration_value)))) _enumerated_case_2)) (show ((M.mulValue (M.mulValue (M.number (1 : ℂ)) (M.number (0 : ℂ))) (M.number (1 : ℂ))) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue (M.number (0 : ℂ)) (M.number (1 : ℂ))))) from h_23331)
                  )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _enumerated_tail))))))
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp h_33) (fun _enumerated_case_2 => (by
                    have h_23624 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_23625 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_23624).1
                          )
                      )
                    have h_23626 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_23624).2.1
                          )
                      )
                    have h_23627 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_23624).2.2
                          )
                      )
                    have h_23628 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_10
                          )
                      )
                    have h_23629 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_23628).1
                          )
                      )
                    have h_23630 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_23628).2.1
                          )
                      )
                    have h_23631 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_23628).2.2
                          )
                      )
                    have h_23651 : Litex.In _value_i3 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (let _setElement_0 := _wd_1_0;
                      let _setElement_1 := _wd_1_1;
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_33
                          )
                      )
                    have h_23655 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_23656 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_23657 : Litex.Same _value_i3 (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_2
                          )
                      )
                    let _object_w77 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_23625) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_23655).trans (h_23656).symm) (show @Eq M.Value _ _ from Eq.refl _) h_23625)));
                    let _wd_1_1 := _value_i3;
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_23625) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_23655).trans (h_23656).symm) (show @Eq M.Value _ _ from Eq.refl _) h_23625)))) (by
                      have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _wd_1_1) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (let _setElement_0 := _wd_1_0;
                          let _setElement_1 := _wd_1_1;
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                            let _atomic_wd_1_0 := _wd_1_0
                            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0))
                        exact h_23651)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _wd_1_1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _wd_1_1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _wd_1_1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _wd_1_1) _finite_tail))))))
                    )))

                    let _object_w78 := (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i3 (Litex.integerToComplex _value_i2 (Litex.inOfSame _wd_1_0 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_23655).trans (h_23656).symm) (show @Eq M.Value _ _ from Eq.refl _) h_23625)) (by
                      have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                        let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (let _setElement_0 := _wd_1_0;
                          let _setElement_1 := _wd_1_1;
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                            let _atomic_wd_1_0 := _wd_1_0
                            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0))
                        exact h_23651)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                    ));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.integerToComplex _wd_1_0 h_23625) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2))))

                    have h_3 : (by
                      let _equal_wd_1_0 := _object_w77
                      let _equal_wd_1_1 := _object_w78
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w77;
                            let _equal_wd_1_1 := _object_w78;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_23625)) * (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_23655).trans (h_23656).symm) (show @Eq M.Value _ _ from Eq.refl _) h_23625)))) * (Litex.NativeBridge.asComplex _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_23651)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            ))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_23625)) * ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_23655).trans (h_23656).symm) (show @Eq M.Value _ _ from Eq.refl _) h_23625))) * (Litex.NativeBridge.asComplex _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_23651)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            )))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i1 _value_i2 ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_23625)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_23655).trans (h_23656).symm) (show @Eq M.Value _ _ from Eq.refl _) h_23625)))) (Litex.NativeBridge.asComplex_spec _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_23651)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            ))) (Litex.NativeBridge.denoteMul _value_i1 (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_23625)) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_23655).trans (h_23656).symm) (show @Eq M.Value _ _ from Eq.refl _) h_23625))) (Litex.NativeBridge.asComplex_spec _value_i3 (by
                              have _finite_member_0 : M.mem (M.negValue (M.number (1 : ℂ))) (Litex.denote (Litex.C (M := M))) := (by
                                let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))
                              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                              have _finite_source : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                                let _atomic_wd_2_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (let _setElement_0 := _wd_1_0;
                                  let _setElement_1 := _wd_1_1;
                                  let _setTail_2 := Litex.emptySet (M := M);
                                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0))
                                exact h_23651)
                              exact (Or.elim ((Litex.SetSemantics.insert_members (M.negValue (M.number (1 : ℂ))) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i3) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _finite_tail))))))
                            )))) (by ring!))))
                          )
                      )
                    have h_27886 : (by
                      let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      (Litex.mul _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))))
                      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
                      let _wd_1_1 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
                      let _wd_2_1 := (_equal_wd_1_0).val.right;
                      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_2_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (- (1 : ℂ))) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))))
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            (Litex.mul _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
                            let _wd_1_1 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
                            let _wd_2_1 := (_equal_wd_1_0).val.right;
                            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_2_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (- (1 : ℂ))) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((1 : ℂ) * (1 : ℂ)) * (- (1 : ℂ))) ((1 : ℂ) * ((1 : ℂ) * (- (1 : ℂ)))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_1).val.right).val.right ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))) (by norm_num))))
                          )
                      )
                    show ((M.mulValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote _value_i1) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))
                    exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue _enumeration_value (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (1 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue _enumeration_value (Litex.denote _value_i3))))) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) _enumeration_value) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue (M.number (1 : ℂ)) _enumeration_value)))) _enumerated_case_2)) (show ((M.mulValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.negValue (M.number (1 : ℂ)))) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue (M.number (1 : ℂ)) (M.negValue (M.number (1 : ℂ)))))) from h_27886)
                  )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _enumerated_tail) (fun _enumerated_case_2 => (by
                    have h_28084 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_28085 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_28084).1
                          )
                      )
                    have h_28086 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_28084).2.1
                          )
                      )
                    have h_28087 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_28084).2.2
                          )
                      )
                    have h_28088 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_10
                          )
                      )
                    have h_28089 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_28088).1
                          )
                      )
                    have h_28090 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_28088).2.1
                          )
                      )
                    have h_28091 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_28088).2.2
                          )
                      )
                    have h_28111 : Litex.In _value_i3 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (let _setElement_0 := _wd_1_0;
                      let _setElement_1 := _wd_1_1;
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (- (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_33
                          )
                      )
                    have h_28115 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_28116 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_28117 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_2
                          )
                      )
                    let _object_w87 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_28085) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28116).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085)));
                    let _wd_1_1 := _value_i3;
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_28085) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28116).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085)))) (Litex.integerToComplex _wd_1_1 (Litex.inOfSame _value_i1 _wd_1_1 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28117).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085))))

                    let _object_w88 := (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i3 (Litex.integerToComplex _value_i2 (Litex.inOfSame _wd_1_0 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28116).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085)) (Litex.integerToComplex _value_i3 (Litex.inOfSame _wd_1_0 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28117).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085)));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.integerToComplex _wd_1_0 h_28085) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC _value_i2 _value_i3 (Litex.integerToComplex _value_i2 (Litex.inOfSame _wd_1_0 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28116).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085)) (Litex.integerToComplex _value_i3 (Litex.inOfSame _wd_1_0 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28117).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085))))))

                    have h_3 : (by
                      let _equal_wd_1_0 := _object_w87
                      let _equal_wd_1_1 := _object_w88
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w87;
                            let _equal_wd_1_1 := _object_w88;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_28085)) * (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28116).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085)))) * (Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i1 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28117).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085)))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_28085)) * ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28116).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085))) * (Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i1 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28117).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085))))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i1 _value_i2 ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_28085)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28116).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085)))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i1 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28117).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085)))) (Litex.NativeBridge.denoteMul _value_i1 (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_28085)) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28116).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inOfSame _value_i1 _value_i3 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_28115).trans (h_28117).symm) (show @Eq M.Value _ _ from Eq.refl _) h_28085))))) (by ring!))))
                          )
                      )
                    have h_29042 : (by
                      let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                      (Litex.mul _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
                      let _wd_1_1 := (_equal_wd_1_0).val.left;
                      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.mul _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))));
                            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
                            let _wd_1_1 := (_equal_wd_1_0).val.left;
                            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                              let _atomic_wd_1_0 := _wd_1_1
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))));
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((1 : ℂ) * (1 : ℂ)) * (1 : ℂ)) ((1 : ℂ) * ((1 : ℂ) * (1 : ℂ))) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (by norm_num))))
                          )
                      )
                    show ((M.mulValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote _value_i1) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))
                    exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = (M.mulValue _enumeration_value (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i3))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (1 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue _enumeration_value (Litex.denote _value_i3))))) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) _enumeration_value) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue (M.number (1 : ℂ)) _enumeration_value)))) _enumerated_case_2)) (show ((M.mulValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.number (1 : ℂ))) = (M.mulValue (M.number (1 : ℂ)) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))))) from h_29042)
                  )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _enumerated_tail))))))
              )
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_triple_x5f_product_x2f_statement_x2e_lit

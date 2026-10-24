import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_mixed_x5f_finite_x5f_product_x5f_commutes_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_11 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), (by
  have h_7 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_6).1
        )
    )
  exact Litex.Same (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_7) (by
    have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
    have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
    have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
      let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
        let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
        let _setTail_2 := Litex.emptySet (M := M);
        let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
        let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0)
      exact h_11)
    exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
  )) (Litex.mul _value_i2 _value_i1 (by
    have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
    have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
    have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
      let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
        let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
        let _setTail_2 := Litex.emptySet (M := M);
        let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
        let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0)
      exact h_11)
    exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
  ) (Litex.integerToComplex _value_i1 h_7))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_11
          have h_7 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_6).1
                )
            )
          have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_6).2.1
                )
            )
          have h_9 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_6).2.2
                )
            )
          change ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i1)))
          exact (by
            obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (0 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) h_6
            have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) ∨ _enumerated_integer = (2 : ℤ) := by omega
            rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp h_11) (fun _enumerated_case_1 => (by
                have h_1709 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_6
                      )
                  )
                have h_1710 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_1709).1
                      )
                  )
                have h_1711 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_1709).2.1
                      )
                  )
                have h_1712 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_1709).2.2
                      )
                  )
                have h_1714 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_11
                      )
                  )
                have h_1718 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_0
                      )
                  )
                have h_1719 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_1
                      )
                  )
                let _object_w12 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_1710) (by
                  have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                  have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                  have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact h_1714)
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                ))

                let _object_w13 := (Litex.mul _value_i2 _value_i1 (by
                  have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                  have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                  have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact h_1714)
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                ) (Litex.integerToComplex _value_i1 h_1710))

                have h_3 : (by
                  let _equal_wd_1_0 := _object_w12
                  let _equal_wd_1_1 := _object_w13
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := _object_w12;
                        let _equal_wd_1_1 := _object_w13;
                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_1710)) * (Litex.NativeBridge.asComplex _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_1714)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        ))) ((Litex.NativeBridge.asComplex _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_1714)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        )) * (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_1710))) (Litex.NativeBridge.denoteMul _value_i1 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_1710)) (Litex.NativeBridge.asComplex_spec _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_1714)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        ))) (Litex.NativeBridge.denoteMul _value_i2 _value_i1 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_1714)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        )) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_1710))) (by ring!))))
                      )
                  )
                have h_3422 : (by
                  let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                  let _equal_wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _equal_wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((0 : ℂ) * (1 : ℂ)) ((1 : ℂ) * (0 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (by norm_num))))
                      )
                  )
                show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i1)))
                exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) _enumeration_value))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.number (0 : ℂ)) _enumeration_value) = (M.mulValue _enumeration_value (M.number (0 : ℂ))))) _enumerated_case_1)) (show ((M.mulValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) = (M.mulValue (M.number (1 : ℂ)) (M.number (0 : ℂ)))) from h_3422)
              )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _enumerated_tail) (fun _enumerated_case_1 => (by
                have h_3466 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_6
                      )
                  )
                have h_3467 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_3466).1
                      )
                  )
                have h_3468 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_3466).2.1
                      )
                  )
                have h_3469 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_3466).2.2
                      )
                  )
                have h_3471 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_11
                      )
                  )
                have h_3475 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_0
                      )
                  )
                have h_3476 : Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_1
                      )
                  )
                let _object_w22 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_3467) (by
                  have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                  have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                  have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact h_3471)
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                ))

                let _object_w23 := (Litex.mul _value_i2 _value_i1 (by
                  have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                  have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                  have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact h_3471)
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                ) (Litex.integerToComplex _value_i1 h_3467))

                have h_3 : (by
                  let _equal_wd_1_0 := _object_w22
                  let _equal_wd_1_1 := _object_w23
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := _object_w22;
                        let _equal_wd_1_1 := _object_w23;
                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_3467)) * (Litex.NativeBridge.asComplex _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_3471)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        ))) ((Litex.NativeBridge.asComplex _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_3471)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        )) * (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_3467))) (Litex.NativeBridge.denoteMul _value_i1 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_3467)) (Litex.NativeBridge.asComplex_spec _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_3471)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        ))) (Litex.NativeBridge.denoteMul _value_i2 _value_i1 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_3471)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        )) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_3467))) (by ring!))))
                      )
                  )
                have h_5179 : (by
                  let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                  let _equal_wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _equal_wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((0 : ℂ) * (2 : ℂ)) ((2 : ℂ) * (0 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (by norm_num))))
                      )
                  )
                show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i1)))
                exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) _enumeration_value))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.number (0 : ℂ)) _enumeration_value) = (M.mulValue _enumeration_value (M.number (0 : ℂ))))) _enumerated_case_1)) (show ((M.mulValue (M.number (0 : ℂ)) (M.number (2 : ℂ))) = (M.mulValue (M.number (2 : ℂ)) (M.number (0 : ℂ)))) from h_5179)
              )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _enumerated_tail))))))
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp h_11) (fun _enumerated_case_1 => (by
                have h_5223 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_6
                      )
                  )
                have h_5224 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_5223).1
                      )
                  )
                have h_5225 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_5223).2.1
                      )
                  )
                have h_5226 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_5223).2.2
                      )
                  )
                have h_5228 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_11
                      )
                  )
                have h_5232 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_0
                      )
                  )
                have h_5233 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_1
                      )
                  )
                let _object_w32 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_5224) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_5232).trans (h_5233).symm) (show @Eq M.Value _ _ from Eq.refl _) h_5224)))

                let _object_w33 := (Litex.mul _value_i2 _value_i1 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_5232).trans (h_5233).symm) (show @Eq M.Value _ _ from Eq.refl _) h_5224)) (Litex.integerToComplex _value_i1 h_5224))

                have h_3 : (by
                  let _equal_wd_1_0 := _object_w32
                  let _equal_wd_1_1 := _object_w33
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (congrArg₂ M.mulValue (show (Litex.denote _value_i1) = (Litex.denote _value_i2) from ((h_5232).trans (h_5233).symm)) (show (Litex.denote _value_i2) = (Litex.denote _value_i1) from ((h_5233).trans (h_5232).symm)))
                      )
                  )
                have h_5407 : (by
                  let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                  let _equal_wd_1_1 := _equal_wd_1_0
                  exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (show @Eq M.Value _ _ from Eq.refl _)
                      )
                  )
                show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i1)))
                exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) _enumeration_value))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.number (1 : ℂ)) _enumeration_value) = (M.mulValue _enumeration_value (M.number (1 : ℂ))))) _enumerated_case_1)) (show ((M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) from h_5407)
              )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _enumerated_tail) (fun _enumerated_case_1 => (by
                have h_5463 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_6
                      )
                  )
                have h_5464 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_5463).1
                      )
                  )
                have h_5465 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_5463).2.1
                      )
                  )
                have h_5466 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_5463).2.2
                      )
                  )
                have h_5468 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_11
                      )
                  )
                have h_5472 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_0
                      )
                  )
                have h_5473 : Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_1
                      )
                  )
                let _object_w42 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_5464) (by
                  have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                  have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                  have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact h_5468)
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                ))

                let _object_w43 := (Litex.mul _value_i2 _value_i1 (by
                  have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                  have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                  have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact h_5468)
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                ) (Litex.integerToComplex _value_i1 h_5464))

                have h_3 : (by
                  let _equal_wd_1_0 := _object_w42
                  let _equal_wd_1_1 := _object_w43
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := _object_w42;
                        let _equal_wd_1_1 := _object_w43;
                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_5464)) * (Litex.NativeBridge.asComplex _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_5468)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        ))) ((Litex.NativeBridge.asComplex _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_5468)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        )) * (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_5464))) (Litex.NativeBridge.denoteMul _value_i1 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_5464)) (Litex.NativeBridge.asComplex_spec _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_5468)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        ))) (Litex.NativeBridge.denoteMul _value_i2 _value_i1 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_5468)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        )) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_5464))) (by ring!))))
                      )
                  )
                have h_7182 : (by
                  let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                  let _equal_wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _equal_wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((1 : ℂ) * (2 : ℂ)) ((2 : ℂ) * (1 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
                      )
                  )
                show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i1)))
                exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) _enumeration_value))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.number (1 : ℂ)) _enumeration_value) = (M.mulValue _enumeration_value (M.number (1 : ℂ))))) _enumerated_case_1)) (show ((M.mulValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = (M.mulValue (M.number (2 : ℂ)) (M.number (1 : ℂ)))) from h_7182)
              )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _enumerated_tail))))))
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (2 : ℂ)))
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp h_11) (fun _enumerated_case_1 => (by
                have h_7226 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_6
                      )
                  )
                have h_7227 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_7226).1
                      )
                  )
                have h_7228 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_7226).2.1
                      )
                  )
                have h_7229 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_7226).2.2
                      )
                  )
                have h_7231 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_11
                      )
                  )
                have h_7235 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_0
                      )
                  )
                have h_7236 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_1
                      )
                  )
                let _object_w53 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_7227) (by
                  have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                  have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                  have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact h_7231)
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                ))

                let _object_w54 := (Litex.mul _value_i2 _value_i1 (by
                  have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                  have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                  have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact h_7231)
                  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                ) (Litex.integerToComplex _value_i1 h_7227))

                have h_3 : (by
                  let _equal_wd_1_0 := _object_w53
                  let _equal_wd_1_1 := _object_w54
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := _object_w53;
                        let _equal_wd_1_1 := _object_w54;
                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_7227)) * (Litex.NativeBridge.asComplex _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_7231)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        ))) ((Litex.NativeBridge.asComplex _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_7231)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        )) * (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_7227))) (Litex.NativeBridge.denoteMul _value_i1 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_7227)) (Litex.NativeBridge.asComplex_spec _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_7231)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        ))) (Litex.NativeBridge.denoteMul _value_i2 _value_i1 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (by
                          have _finite_member_0 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                          have _finite_member_1 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                          have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                              let _setTail_2 := Litex.emptySet (M := M);
                              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)
                            exact h_7231)
                          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                        )) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_7227))) (by ring!))))
                      )
                  )
                have h_8945 : (by
                  let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                  let _equal_wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _equal_wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((2 : ℂ) * (1 : ℂ)) ((1 : ℂ) * (2 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))))
                      )
                  )
                show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i1)))
                exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) _enumeration_value))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.number (2 : ℂ)) _enumeration_value) = (M.mulValue _enumeration_value (M.number (2 : ℂ))))) _enumerated_case_1)) (show ((M.mulValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = (M.mulValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) from h_8945)
              )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _enumerated_tail) (fun _enumerated_case_1 => (by
                have h_8989 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_6
                      )
                  )
                have h_8990 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_8989).1
                      )
                  )
                have h_8991 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_8989).2.1
                      )
                  )
                have h_8992 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_8989).2.2
                      )
                  )
                have h_8994 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_11
                      )
                  )
                have h_8998 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_0
                      )
                  )
                have h_8999 : Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case_1
                      )
                  )
                let _object_w63 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_8990) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_8998).trans (h_8999).symm) (show @Eq M.Value _ _ from Eq.refl _) h_8990)))

                let _object_w64 := (Litex.mul _value_i2 _value_i1 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_8998).trans (h_8999).symm) (show @Eq M.Value _ _ from Eq.refl _) h_8990)) (Litex.integerToComplex _value_i1 h_8990))

                have h_3 : (by
                  let _equal_wd_1_0 := _object_w63
                  let _equal_wd_1_1 := _object_w64
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (congrArg₂ M.mulValue (show (Litex.denote _value_i1) = (Litex.denote _value_i2) from ((h_8998).trans (h_8999).symm)) (show (Litex.denote _value_i2) = (Litex.denote _value_i1) from ((h_8999).trans (h_8998).symm)))
                      )
                  )
                have h_9173 : (by
                  let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                  let _equal_wd_1_1 := _equal_wd_1_0
                  exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (show @Eq M.Value _ _ from Eq.refl _)
                      )
                  )
                show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i1)))
                exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) _enumeration_value))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.number (2 : ℂ)) _enumeration_value) = (M.mulValue _enumeration_value (M.number (2 : ℂ))))) _enumerated_case_1)) (show ((M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ)))) from h_9173)
              )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _enumerated_tail))))))
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_mixed_x5f_finite_x5f_product_x5f_commutes_x2f_statement_x2e_lit

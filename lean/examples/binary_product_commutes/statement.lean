import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_binary_x5f_product_x5f_commutes_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Same (Litex.mul _value_i1 _value_i2 (by
  have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
  have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
  have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact h_5)
  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
) (by
  have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
  have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
  have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact h_9)
  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
)) (Litex.mul _value_i2 _value_i1 (by
  have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
  have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
  have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact h_9)
  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
) (by
  have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
  have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
  have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact h_5)
  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_9
          change ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i1)))
          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp h_5) (fun _enumerated_case_0 => (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp h_9) (fun _enumerated_case_1 => (by
            have h_2590 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_5
                  )
              )
            have h_2594 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_9
                  )
              )
            have h_2598 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case_0
                  )
              )
            have h_2599 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case_1
                  )
              )
            let _object_w4 := (Litex.mul _value_i1 _value_i2 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_2590)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (Litex.inOfSame _value_i1 _value_i2 _atomic_wd_2_1 _atomic_wd_2_1 ((h_2598).trans (h_2599).symm) (show @Eq M.Value _ _ from Eq.refl _) h_2590))
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
            ))

            let _object_w5 := (Litex.mul _value_i2 _value_i1 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (Litex.inOfSame _value_i1 _value_i2 _atomic_wd_2_1 _atomic_wd_2_1 ((h_2598).trans (h_2599).symm) (show @Eq M.Value _ _ from Eq.refl _) h_2590))
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_2590)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
            ))

            have h_3 : (by
              let _equal_wd_1_0 := _object_w4
              let _equal_wd_1_1 := _object_w5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg₂ M.mulValue (show (Litex.denote _value_i1) = (Litex.denote _value_i2) from ((h_2598).trans (h_2599).symm)) (show (Litex.denote _value_i2) = (Litex.denote _value_i1) from ((h_2599).trans (h_2598).symm)))
                  )
              )
            have h_6045 : (by
              let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
              let _equal_wd_1_1 := _equal_wd_1_0
              exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show @Eq M.Value _ _ from Eq.refl _)
                  )
              )
            show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i1)))
            exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) _enumeration_value))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.number (0 : ℂ)) _enumeration_value) = (M.mulValue _enumeration_value (M.number (0 : ℂ))))) _enumerated_case_1)) (show ((M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) = (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ)))) from h_6045)
          )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _enumerated_tail) (fun _enumerated_case_1 => (by
            have h_6084 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_5
                  )
              )
            have h_6088 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_9
                  )
              )
            have h_6092 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case_0
                  )
              )
            have h_6093 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case_1
                  )
              )
            let _object_w10 := (Litex.mul _value_i1 _value_i2 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_6084)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_6088)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
            ))

            let _object_w11 := (Litex.mul _value_i2 _value_i1 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_6088)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_6084)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
            ))

            have h_3 : (by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w11
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w10;
                    let _equal_wd_1_1 := _object_w11;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6084)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
                    )) * (Litex.NativeBridge.asComplex _value_i2 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6088)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                    ))) ((Litex.NativeBridge.asComplex _value_i2 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6088)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                    )) * (Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6084)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
                    ))) (Litex.NativeBridge.denoteMul _value_i1 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6084)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
                    )) (Litex.NativeBridge.asComplex_spec _value_i2 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6088)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                    ))) (Litex.NativeBridge.denoteMul _value_i2 _value_i1 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6088)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                    )) (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6084)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
                    ))) (by ring!))))
                  )
              )
            have h_8690 : (by
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
            exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) _enumeration_value))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.number (0 : ℂ)) _enumeration_value) = (M.mulValue _enumeration_value (M.number (0 : ℂ))))) _enumerated_case_1)) (show ((M.mulValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) = (M.mulValue (M.number (1 : ℂ)) (M.number (0 : ℂ)))) from h_8690)
          )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _enumerated_tail))))))) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _enumerated_tail) (fun _enumerated_case_0 => (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp h_9) (fun _enumerated_case_1 => (by
            have h_8721 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_5
                  )
              )
            have h_8725 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_9
                  )
              )
            have h_8729 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case_0
                  )
              )
            have h_8730 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case_1
                  )
              )
            let _object_w17 := (Litex.mul _value_i1 _value_i2 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_8721)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_8725)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
            ))

            let _object_w18 := (Litex.mul _value_i2 _value_i1 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_8725)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_8721)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
            ))

            have h_3 : (by
              let _equal_wd_1_0 := _object_w17
              let _equal_wd_1_1 := _object_w18
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w17;
                    let _equal_wd_1_1 := _object_w18;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_8721)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
                    )) * (Litex.NativeBridge.asComplex _value_i2 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_8725)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                    ))) ((Litex.NativeBridge.asComplex _value_i2 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_8725)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                    )) * (Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_8721)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
                    ))) (Litex.NativeBridge.denoteMul _value_i1 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_8721)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
                    )) (Litex.NativeBridge.asComplex_spec _value_i2 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_8725)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                    ))) (Litex.NativeBridge.denoteMul _value_i2 _value_i1 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_8725)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
                    )) (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setTail_2 := Litex.emptySet (M := M);
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_8721)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
                    ))) (by ring!))))
                  )
              )
            have h_11327 : (by
              let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
              let _equal_wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                    let _equal_wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((1 : ℂ) * (0 : ℂ)) ((0 : ℂ) * (1 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
                  )
              )
            show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i1)))
            exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) _enumeration_value))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.number (1 : ℂ)) _enumeration_value) = (M.mulValue _enumeration_value (M.number (1 : ℂ))))) _enumerated_case_1)) (show ((M.mulValue (M.number (1 : ℂ)) (M.number (0 : ℂ))) = (M.mulValue (M.number (0 : ℂ)) (M.number (1 : ℂ)))) from h_11327)
          )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _enumerated_tail) (fun _enumerated_case_1 => (by
            have h_11358 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_5
                  )
              )
            have h_11362 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_9
                  )
              )
            have h_11366 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case_0
                  )
              )
            have h_11367 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case_1
                  )
              )
            let _object_w23 := (Litex.mul _value_i1 _value_i2 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_11358)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (Litex.inOfSame _value_i1 _value_i2 _atomic_wd_2_1 _atomic_wd_2_1 ((h_11366).trans (h_11367).symm) (show @Eq M.Value _ _ from Eq.refl _) h_11358))
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
            ))

            let _object_w24 := (Litex.mul _value_i2 _value_i1 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (Litex.inOfSame _value_i1 _value_i2 _atomic_wd_2_1 _atomic_wd_2_1 ((h_11366).trans (h_11367).symm) (show @Eq M.Value _ _ from Eq.refl _) h_11358))
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i2) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _finite_tail))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_11358)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))
            ))

            have h_3 : (by
              let _equal_wd_1_0 := _object_w23
              let _equal_wd_1_1 := _object_w24
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg₂ M.mulValue (show (Litex.denote _value_i1) = (Litex.denote _value_i2) from ((h_11366).trans (h_11367).symm)) (show (Litex.denote _value_i2) = (Litex.denote _value_i1) from ((h_11367).trans (h_11366).symm)))
                  )
              )
            have h_14813 : (by
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
            exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value (Litex.denote _value_i2)) = (M.mulValue (Litex.denote _value_i2) _enumeration_value))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue (M.number (1 : ℂ)) _enumeration_value) = (M.mulValue _enumeration_value (M.number (1 : ℂ))))) _enumerated_case_1)) (show ((M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) from h_14813)
          )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _enumerated_tail))))))) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _enumerated_tail))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_binary_x5f_product_x5f_commutes_x2f_statement_x2e_lit

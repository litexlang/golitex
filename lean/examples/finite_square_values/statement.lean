import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_square_x5f_values_x2f_statement_x2e_lit

universe u v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Same (Litex.mul _value_i1 _value_i1 (by
  have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
  have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
  have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
  have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_3 := Litex.emptySet (M := M);
      let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
      let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact h_7)
  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
) (by
  have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
  have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
  have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
  have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_3 := Litex.emptySet (M := M);
      let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
      let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact h_7)
  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
)) (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
  have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
  have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
  have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
  have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_3 := Litex.emptySet (M := M);
      let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
      let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact h_7)
  exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7
          change ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.powValue (Litex.denote _value_i1) (M.number (2 : ℂ))))
          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp h_7) (fun _enumerated_case => (by
            have h_1355 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_3 := Litex.emptySet (M := M);
              let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
              let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_7
                  )
              )
            have h_1360 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case
                  )
              )
            let _object_w4 := (Litex.mul _value_i1 _value_i1 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_3 := Litex.emptySet (M := M);
                  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_1355)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_3 := Litex.emptySet (M := M);
                  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_1355)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
            ))

            let _object_w5 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
              have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_3 := Litex.emptySet (M := M);
                  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_1355)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
            ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))

            have h_3 : (by
              let _equal_wd_1_0 := _object_w4
              let _equal_wd_1_1 := _object_w5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w4;
                    let _equal_wd_1_1 := _object_w5;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_1355)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    )) * (Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_1355)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ))) ((Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_1355)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    )) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_1355)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    )) (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_1355)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_1355)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_1355)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ))) (by ring!))))
                  )
              )
            have h_3663 : (by
              let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
              let _equal_wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                    let _equal_wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((0 : ℂ) * (0 : ℂ)) ((0 : ℂ) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (by norm_num))))
                  )
              )
            show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.powValue (Litex.denote _value_i1) (M.number (2 : ℂ))))
            exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value _enumeration_value) = (M.powValue _enumeration_value (M.number (2 : ℂ))))) _enumerated_case) (show ((M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) = (M.powValue (M.number (0 : ℂ)) (M.number (2 : ℂ)))) from h_3663)
          )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _enumerated_tail) (fun _enumerated_case => (by
            have h_3929 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_3 := Litex.emptySet (M := M);
              let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
              let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_7
                  )
              )
            have h_3934 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case
                  )
              )
            let _object_w10 := (Litex.mul _value_i1 _value_i1 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_3 := Litex.emptySet (M := M);
                  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_3929)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_3 := Litex.emptySet (M := M);
                  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_3929)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
            ))

            let _object_w11 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
              have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_3 := Litex.emptySet (M := M);
                  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_3929)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
            ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))

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
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_3929)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    )) * (Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_3929)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ))) ((Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_3929)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    )) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_3929)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    )) (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_3929)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_3929)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_3929)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ))) (by ring!))))
                  )
              )
            have h_6221 : (by
              let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
              let _equal_wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _equal_wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((1 : ℂ) * (1 : ℂ)) ((1 : ℂ) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
                  )
              )
            have h_6251 : Litex.In (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.RPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have h_6241 : (by
                      let _atomic_wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                      let _atomic_wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                      exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                        let _atomic_wd_2_0 := _atomic_wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) ^ (2 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) ^ (2 : ℕ)) (1 : ℝ) (by norm_num))))).mpr (by
                        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                        have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                        let _atomic_wd_2_0 := _atomic_wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) ^ (2 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) ^ (2 : ℕ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                        let _atomic_wd_2_0 := _atomic_wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) ^ (2 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) ^ (2 : ℕ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                      have h_6248 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                      exact Litex.inOfSame (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Eq.symm h_6221) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_6241; exact (M.real_members (Litex.denote (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))).mpr ⟨_litex_real, _litex_value⟩) h_6241)
                    )
                  )
              )
            show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.powValue (Litex.denote _value_i1) (M.number (2 : ℂ))))
            exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value _enumeration_value) = (M.powValue _enumeration_value (M.number (2 : ℂ))))) _enumerated_case) (show ((M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.powValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) from h_6221)
          )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _enumerated_tail) (fun _enumerated_case => (by
            have h_6255 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_3 := Litex.emptySet (M := M);
              let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
              let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_7
                  )
              )
            have h_6260 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case
                  )
              )
            let _object_w17 := (Litex.mul _value_i1 _value_i1 (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_3 := Litex.emptySet (M := M);
                  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_6255)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
            ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
              have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_3 := Litex.emptySet (M := M);
                  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_6255)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
            ))

            let _object_w18 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
              have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
              have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
              have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_3 := Litex.emptySet (M := M);
                  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_6255)
              exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
            ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))

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
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6255)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    )) * (Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6255)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ))) ((Litex.NativeBridge.asComplex _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6255)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    )) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6255)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    )) (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6255)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.R (M := M))) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6255)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.R (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.R (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (by
                      have _finite_member_0 : M.mem (M.number (0 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (0 : ℂ))
                      have _finite_member_1 : M.mem (M.number (1 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (1 : ℂ))
                      have _finite_member_2 : M.mem (M.number (2 : ℂ)) (Litex.denote (Litex.C (M := M))) := (Litex.numberInC (M := M) (2 : ℂ))
                      have _finite_source : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                          let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
                          let _setTail_3 := Litex.emptySet (M := M);
                          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_6255)
                      exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (Litex.denote _value_i1)).mp _finite_source) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_0)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_1)) (fun _finite_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp _finite_tail) (fun _finite_case => (show M.mem (Litex.denote _value_i1) (Litex.denote (Litex.C (M := M))) from Eq.mpr (congrArg (fun _v => M.mem _v (Litex.denote (Litex.C (M := M)))) _finite_case) _finite_member_2)) (fun _finite_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _finite_tail))))))))
                    ))) (by ring!))))
                  )
              )
            have h_8549 : (by
              let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
              let _equal_wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                    let _equal_wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((2 : ℂ) * (2 : ℂ)) ((2 : ℂ) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))))
                  )
              )
            have h_8583 : Litex.In (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.RPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have h_8571 : (by
                      let _atomic_wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                      let _atomic_wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                      exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                        let _atomic_wd_2_0 := _atomic_wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (2 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) ^ (2 : ℕ)) (4 : ℝ) (by norm_num))))).mpr (by
                        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                        have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                        let _atomic_wd_2_0 := _atomic_wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (2 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) ^ (2 : ℕ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                        let _atomic_wd_2_0 := _atomic_wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (2 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) ^ (2 : ℕ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                      have h_8578 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                      exact Litex.inOfSame (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Eq.symm h_8549) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_8571; exact (M.real_members (Litex.denote (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))).mpr ⟨_litex_real, _litex_value⟩) h_8571)
                    )
                  )
              )
            show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.powValue (Litex.denote _value_i1) (M.number (2 : ℂ))))
            exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value _enumeration_value) = (M.powValue _enumeration_value (M.number (2 : ℂ))))) _enumerated_case) (show ((M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = (M.powValue (M.number (2 : ℂ)) (M.number (2 : ℂ)))) from h_8549)
          )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _enumerated_tail))))))))
        )
      )
  )

theorem h_9935 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9940 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), ((Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_9940
          change ((((Litex.denote _value_i2) = (M.number (0 : ℂ)))) ∨ (((Litex.denote _value_i2) = (M.number (1 : ℂ)))))
          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i2)).mp h_9940) (fun _enumerated_case => (by
            have h_9945 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
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
                    h_9940
                  )
              )
            have h_9949 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case
                  )
              )
            have h_9938 : ((Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)))) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      classical
                      apply Classical.byContradiction
                      intro _negative_disjunction
                      have h_9950 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _branch => _negative_disjunction (Or.inr _branch))
                            )
                        )
                      exact _negative_disjunction (Or.inl h_9949)
                    )
                  )
              )
            have h_9954 : ((Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)))) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      classical
                      have _factor_real_0 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
                      have _factor_real_1 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                      let _product := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                      have _product_zero : Litex.Same _product (Litex.number 0) := (let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((0 : ℂ) * (1 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
                      by_cases _left : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ))
                      · exact Or.inl _left
                      · apply Or.inr
                        apply Classical.byContradiction
                        intro _right
                        exact (Litex.mulNonzero _product.val.left _product.val.right _product.wd.1 _product.wd.2 _left (fun h => _right h.symm)) _product_zero
                    )
                  )
              )
            show ((((Litex.denote _value_i2) = (M.number (0 : ℂ)))) ∨ (((Litex.denote _value_i2) = (M.number (1 : ℂ)))))
            exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (((_enumeration_value = (M.number (0 : ℂ)))) ∨ ((_enumeration_value = (M.number (1 : ℂ)))))) _enumerated_case) (show ((((M.number (0 : ℂ)) = (M.number (0 : ℂ)))) ∨ (((M.number (0 : ℂ)) = (M.number (1 : ℂ))))) from h_9954)
          )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i2)).mp _enumerated_tail) (fun _enumerated_case => (by
            have h_9974 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
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
                    h_9940
                  )
              )
            have h_9978 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case
                  )
              )
            have h_9938 : ((Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)))) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      classical
                      apply Classical.byContradiction
                      intro _negative_disjunction
                      have h_10029 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _branch => _negative_disjunction (Or.inl _branch))
                            )
                        )
                      exact _negative_disjunction (Or.inr h_9978)
                    )
                  )
              )
            have h_10033 : ((Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)))) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      classical
                      apply Classical.byContradiction
                      intro _negative_disjunction
                      have h_10059 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _branch => _negative_disjunction (Or.inl _branch))
                            )
                        )
                      exact _negative_disjunction (Or.inr (show @Eq M.Value _ _ from Eq.refl _))
                    )
                  )
              )
            show ((((Litex.denote _value_i2) = (M.number (0 : ℂ)))) ∨ (((Litex.denote _value_i2) = (M.number (1 : ℂ)))))
            exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (((_enumeration_value = (M.number (0 : ℂ)))) ∨ ((_enumeration_value = (M.number (1 : ℂ)))))) _enumerated_case) (show ((((M.number (1 : ℂ)) = (M.number (0 : ℂ)))) ∨ (((M.number (1 : ℂ)) = (M.number (1 : ℂ))))) from h_10033)
          )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i2) _enumerated_tail))))))
        )
      )
  )

theorem h_10068 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10071 : Litex.In _value_i3 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)) (h_10066 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_10071 h_10066
          change ((Litex.denote _value_i3) = (M.number (1 : ℂ)))
          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i3)).mp h_10071) (fun _enumerated_case => (by
            have h_10076 : Litex.In _value_i3 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
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
                    h_10071
                  )
              )
            have h_10080 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case
                  )
              )
            have _excluded : ¬ ((¬ ((Litex.denote _value_i3) = (M.number (0 : ℂ))))) := by
              have _negative : ((M.number (0 : ℂ)) = (M.number (0 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
              intro _source_guard
              have _actual_guard := Eq.mp (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case) _source_guard
              exact _actual_guard _negative
            exact False.elim (_excluded h_10066)
          )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i3)).mp _enumerated_tail) (fun _enumerated_case => (by
            have h_10085 : Litex.In _value_i3 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
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
                    h_10071
                  )
              )
            have h_10089 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case
                  )
              )
            have h_10090 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case) h_10066)
                  )
              )
            have h_10069 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_10089
                  )
              )
            have h_10117 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (show @Eq M.Value _ _ from Eq.refl _)
                  )
              )
            show ((Litex.denote _value_i3) = (M.number (1 : ℂ)))
            exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (_enumeration_value = (M.number (1 : ℂ)))) _enumerated_case) (show ((M.number (1 : ℂ)) = (M.number (1 : ℂ))) from h_10117)
          )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i3) _enumerated_tail))))))
        )
      )
  )

theorem h_10125 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_10127 : Litex.In _value_i4 (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0)), Litex.Same _value_i4 _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_10127
          change ((Litex.denote _value_i4) = (Litex.denote _value_i4))
          exact (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i4) h_10127))
        )
      )
  )

theorem h_10131 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10137 : Litex.In _value_i5 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)) (h_10129 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_10137 h_10129
          have h_10142 : Litex.In _value_i5 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
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
                  h_10137
                )
            )
          have h_10134 : ∀ (_enumerated_i6 : M.Value) (h_10146 : M.mem _enumerated_i6 (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) (h_10132 : (¬ (_enumerated_i6 = (M.number (0 : ℂ))))), (_enumerated_i6 = (M.number (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _enumerated_i6 h_10146 h_10132
                    let _value_i6 := Litex.semanticObject _enumerated_i6 (M.member_isSet h_10146)
                    change ((Litex.denote _value_i6) = (M.number (1 : ℂ)))
                    exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.insertValue (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i6)).mp h_10146) (fun _enumerated_case => (by
                      have h_10151 : Litex.In _value_i6 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
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
                              h_10146
                            )
                        )
                      have h_10155 : Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              _enumerated_case
                            )
                        )
                      have _excluded : ¬ ((¬ ((Litex.denote _value_i6) = (M.number (0 : ℂ))))) := by
                        have _negative : ((M.number (0 : ℂ)) = (M.number (0 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                        intro _source_guard
                        have _actual_guard := Eq.mp (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case) _source_guard
                        exact _actual_guard _negative
                      exact False.elim (_excluded h_10132)
                    )) (fun _enumerated_tail => (Or.elim ((Litex.SetSemantics.insert_members (M.number (1 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i6)).mp _enumerated_tail) (fun _enumerated_case => (by
                      have h_10159 : Litex.In _value_i6 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
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
                              h_10146
                            )
                        )
                      have h_10163 : Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              _enumerated_case
                            )
                        )
                      have h_10164 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (show (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case) h_10132)
                            )
                        )
                      have h_10135 : Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              h_10163
                            )
                        )
                      have h_10254 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (show @Eq M.Value _ _ from Eq.refl _)
                            )
                        )
                      show ((Litex.denote _value_i6) = (M.number (1 : ℂ)))
                      exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (_enumeration_value = (M.number (1 : ℂ)))) _enumerated_case) (show ((M.number (1 : ℂ)) = (M.number (1 : ℂ))) from h_10254)
                    )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i6) _enumerated_tail))))))
                  )
                )
            )
          exact (by
            have h_10271 : (by
              let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                let _setTail_2 := Litex.emptySet (M := M);
                let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact Litex.In _value_i5 _atomic_wd_1_1) :=
              (by
                let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
                  let _setTail_2 := Litex.emptySet (M := M);
                  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact h_10142)
            have h_10276 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
              h_10129
            exact (Eq.trans (Eq.symm (Litex.sameRefl _value_i5)) (Eq.trans ((fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value : Litex.Obj (M := M) _Host) => h_10134 (Litex.denote _value)) _value_i5 h_10271 h_10276) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_square_x5f_values_x2f_statement_x2e_lit

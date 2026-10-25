import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_cartesian_x5f_coordinates_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_1 : (by
  let _atomic_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))
  exact Litex.IsNonempty _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))
  exact (Litex.cartNonemptyOfFactors _atomic_wd_1_0 (by
    have _finiteProof_0 := ((Litex.standardNonempty (M := M) Litex.StandardSetValue.real))
    have _finiteProof_1 := ((Litex.standardNonempty (M := M) Litex.StandardSetValue.integer))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )))

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i)))))

noncomputable def _object_h5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) := (Litex.cartCall _value_i1 _ (Litex.number (M := M) (1 : ℂ)) h_4 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

theorem h_5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) : Litex.In (_object_h5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4 (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

noncomputable def _object_h6 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) := (Litex.cartCall _value_i1 _ (Litex.number (M := M) (2 : ℂ)) h_4 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

theorem h_6 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) : Litex.In (_object_h6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4) (Litex.Z (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4 (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_26 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) : Litex.In _value_i1 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _membership_function := _value_i1
          let _membership_target := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_21 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_21)
              have h_21 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_21
              have h_22 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_21).1
                    )
                )
              have h_23 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_21).2.1
                    )
                )
              have h_24 : Litex.Le _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_21).2.2
                    )
                )
              have h_25 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_21)
                    )
                )
              exact True.intro);
            Litex.fnSet (let _litex_output := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))
          have h_27 : ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_139 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (by
            let _object_w14 := (Litex.cartCall _value_i1 _ _value_i2 h_4 (Litex.indexSetMemberOfClosedRangeOfEq (n := 2) (2 : ℂ) (by norm_num) (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact h_139)))
            let _object_w15 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := _object_w14
              let _atomic_wd_1_1 := _object_w15
              exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
          ) := (by
            intro _Host_i2 _rep_i2 _value_i2 h_139
            have h_140 : Litex.In _value_i2 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_139).1
                  )
              )
            have h_141 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_139).2.1
                  )
              )
            have h_142 : Litex.Le _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_139).2.2
                  )
              )
            have h_143 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_139)
                  )
              )
            let _object_w14 := (Litex.cartCall _value_i1 _ _value_i2 h_4 (Litex.indexSetMemberOfClosedRangeOfEq (n := 2) (2 : ℂ) (by norm_num) (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact h_139)))
            let _object_w15 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            have h_28 : (by
              let _atomic_wd_1_0 := _object_w14
              let _atomic_wd_1_1 := _object_w15
              exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      let _atomic_wd_1_0 := _object_w14
                      let _atomic_wd_1_1 := _object_w15
                      exact (by
                        let _receiver := _value_i1
                        let _argument := _value_i2
                        let _target := _atomic_wd_1_1
                        let _call := _atomic_wd_1_0
                        let _source_cart := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))
                        have _source_member : Litex.In _receiver _source_cart := h_4
                        have _returns : ∀ i : Fin 2, M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _receiver) (Litex.FiniteFunction.index i)) (Litex.denote _target) := (by
                        have _finiteProof_0 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _receiver) (Litex.FiniteFunction.index (0 : Fin 2))) (Litex.denote _target) from ((show Litex.Subset (Litex.R (M := M)) _target from (by
                          let _atomic_wd_2_1 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                          exact (fun _x _hx => (Litex.SetSemantics.union_members (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.Z (M := M))) _x).mpr (Or.inl _hx)))) _ (Litex.FiniteFunction.coordinate_mem _source_member (0 : Fin 2)))))
                        have _finiteProof_1 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _receiver) (Litex.FiniteFunction.index (1 : Fin 2))) (Litex.denote _target) from ((show Litex.Subset (Litex.Z (M := M)) _target from (by
                          let _atomic_wd_2_1 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                          exact (fun _x _hx => (Litex.SetSemantics.union_members (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.Z (M := M))) _x).mpr (Or.inr _hx)))) _ (Litex.FiniteFunction.coordinate_mem _source_member (1 : Fin 2)))))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                        have _input : M.mem (Litex.denote _argument) (Litex.FiniteFunction.indexSet (M := M) 2) := _call.wd.2
                        obtain ⟨_index, _hi⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := 2) (Litex.denote _argument)).mp _input
                        change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _receiver) (Litex.denote _argument)) (Litex.denote _target)
                        rw [_hi]
                        exact _returns _index))
                  )
              )
            have h_379 : ((Litex.In _object_w14 (Litex.R (M := M))) ∨ (Litex.In _object_w14 (Litex.Z (M := M)))) :=
              (by
                litex_checked_step =>
                  exact (
                    ((Litex.inUnion_iff _object_w14 (Litex.R (M := M)) (Litex.Z (M := M))).mp h_28)
                  )
              )
            exact h_28
          )
          exact (by
          let _source_cart := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))
          have _source_member : Litex.In _membership_function _source_cart := h_4
          have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) 2 := by
            change Litex.finiteSeqDomain (Litex.number (M := M) (2 : ℂ)) = _
            exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) (2 : ℂ)) 2 (by change M.number (2 : ℂ) = M.number ((2 : ℕ) : ℂ); norm_num)
          apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain
          intro _input _hin
          change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
          obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
          let _raw_0 := _input
          have _member_0 := _members
          let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
          exact h_27 _arg_0 _member_0))
      )
  )

noncomputable def _object_h408 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))

theorem h_408 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) : Litex.In _value_i1 (_object_h408 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame _value_i1 _value_i1 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (_object_h408 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4) (Litex.sameRefl _value_i1) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (h_26 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4))
      )
  )

theorem h_392 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) : (by
  let _atomic_wd_1_0 := (_object_h5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4)
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_h5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4)
          exact (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4))
      )
  )

theorem h_399 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) : (by
  let _atomic_wd_1_0 := (_object_h6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4)
  exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_h6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4)
          exact (h_6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4))
      )
  )

theorem h_409 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) : (by
  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))
  exact Litex.In _value_i1 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))
          exact (h_26 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4))
      )
  )

noncomputable def _object_h422 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))

theorem h_422 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) : Litex.In _value_i1 (_object_h422 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame _value_i1 _value_i1 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (_object_h422 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4) (Litex.sameRefl _value_i1) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (h_409 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4))
      )
  )

theorem h_423 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) : (by
  let _atomic_wd_1_0 := (_object_h5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4)
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_h5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4)
          exact (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4))
      )
  )

theorem h_430 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))) : (by
  let _atomic_wd_1_0 := (_object_h6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4)
  exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_h6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4)
          exact (h_6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_4))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_cartesian_x5f_coordinates_x2f_statement_x2e_lit

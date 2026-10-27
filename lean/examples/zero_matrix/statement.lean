import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_zero_x5f_matrix_x2f_statement_x2e_lit

universe u v1 v2 v19 v20 v21 v22
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.N (M := M))), (by
  let _object_w3 := (Litex.zeroMatrix _value_i1 _value_i2 h_16 h_18)
  let _object_w4 := (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_16 h_18)
  let _object_w6 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_16 h_18)
  exact (((by
    let _atomic_wd_1_0 := _object_w3
    let _atomic_wd_1_1 := _object_w4
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w3
    let _atomic_wd_1_1 := _object_w6
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_18
          have h_17 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_16)
                )
            )
          have h_19 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_18)
                )
            )
          let _object_w3 := (Litex.zeroMatrix _value_i1 _value_i2 h_16 h_18)
          let _object_w4 := (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_16 h_18)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w3
            let _atomic_wd_1_1 := _object_w4
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    let _atomic_wd_1_1 := _object_w4
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix))))
                )
            )
          let _object_h53 := (Litex.fnSet (Litex.matrixSignature _object_w4))
          have h_53 : Litex.In _object_w3 _object_h53 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w3 _object_w3 _object_w4 _object_h53 (Litex.sameRefl _object_w3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet _object_w4)) h_1)
                )
            )
          let _object_w6 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_16 h_18)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w3
            let _atomic_wd_1_1 := _object_w6
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    let _atomic_wd_1_1 := _object_w6
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))
                )
            )
          let _object_h92 := (Litex.fnSet (Litex.matrixSignature _object_w6))
          have h_92 : Litex.In _object_w3 _object_h92 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w3 _object_w3 _object_w6 _object_h92 (Litex.sameRefl _object_w3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet _object_w6)) h_2)
                )
            )
          exact (And.intro h_1 h_2)
        )
      )
  )

theorem h_94 : ∀ {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_113 : Litex.In _value_i19 (Litex.N (M := M))) {_Host_i20 : Type v20} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_115 : Litex.In _value_i20 (Litex.N (M := M))) {_Host_i21 : Type v21} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_135 : Litex.In _value_i21 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_113))) {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_174 : Litex.In _value_i22 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_115))), (by
  let _object_w15 := (let _litex_matrix_head := (Litex.zeroMatrix _value_i19 _value_i20 h_113 h_115);
  (let _litex_call_arg_0 := _value_i21;
  let _litex_call_arg_1 := _value_i22;
  Litex.callOn (Litex.zeroMatrixSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.zeroMatrixInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_113))
    exact h_135) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_115))
    exact h_174)), True.intro⟩)))
  exact (by
    let _equal_wd_1_0 := _object_w15
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i19 _rep_i19 _value_i19 h_113 _Host_i20 _rep_i20 _value_i20 h_115 _Host_i21 _rep_i21 _value_i21 h_135 _Host_i22 _rep_i22 _value_i22 h_174
          have h_114 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i19 h_113)
                )
            )
          have h_116 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i20 h_115)
                )
            )
          have h_136 : Litex.In _value_i21 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_113)) _value_i21 h_135).1
                )
            )
          have h_137 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i21 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_113)) _value_i21 h_135).2.1
                )
            )
          have h_138 : Litex.Le _value_i21 _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_113)) _value_i21 h_135).2.2
                )
            )
          have h_139 : Litex.In _value_i21 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_113)) _value_i21 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_135)
                )
            )
          have h_175 : Litex.In _value_i22 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_115)) _value_i22 h_174).1
                )
            )
          have h_176 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_115)) _value_i22 h_174).2.1
                )
            )
          have h_177 : Litex.Le _value_i22 _value_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_115)) _value_i22 h_174).2.2
                )
            )
          have h_178 : Litex.In _value_i22 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_115)) _value_i22 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_174)
                )
            )
          let _object_w15 := (let _litex_matrix_head := (Litex.zeroMatrix _value_i19 _value_i20 h_113 h_115);
          (let _litex_call_arg_0 := _value_i21;
          let _litex_call_arg_1 := _value_i22;
          Litex.callOn (Litex.zeroMatrixSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.zeroMatrixInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_113))
            exact h_135) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_115))
            exact h_174)), True.intro⟩)))
          have h_93 : (by
            let _equal_wd_1_0 := _object_w15
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w15;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (((show Litex.denote _equal_wd_1_0 = M.number 0 from (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i21 _value_i22))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.zeroMatrixCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i21 _value_i22)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_113))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_115)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_113)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_115)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i29 : M.Value) (_raw_i30 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i21 _value_i22))).mpr ⟨(Litex.callArguments2_mem_cart _value_i21 _value_i22 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_113))
                    exact h_135) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_115))
                    exact h_174)), True.intro⟩))).trans (show (M.number 0) = (Litex.denote (Litex.number (M := M) (0 : ℂ))) from rfl)).trans (show @Eq M.Value _ _ from Eq.refl _))))
                )
            )
          exact h_93
        )
      )
  )

noncomputable def _object_w16 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))

noncomputable def _object_w17 := (Litex.matrixSet (Litex.R (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))

theorem h_306 : (by
  let _atomic_wd_1_0 := (_object_w16 (M := M))
  let _atomic_wd_1_1 := (_object_w17 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w16 (M := M))
          let _atomic_wd_1_1 := (_object_w17 (M := M))
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix))))
      )
  )

noncomputable def _object_h312 := (Litex.fnSet (Litex.matrixSignature (_object_w17 (M := M))))

theorem h_312 : Litex.In (_object_w16 (M := M)) (_object_h312 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (_object_w16 (M := M)) (_object_w16 (M := M)) (_object_w17 (M := M)) (_object_h312 (M := M)) (Litex.sameRefl (_object_w16 (M := M))) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (_object_w17 (M := M)))) (h_306 (M := M)))
      )
  )

noncomputable def _object_w19 := (let _litex_matrix_head := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)));
(let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
let _litex_call_arg_1 := (Litex.number (M := M) (2 : ℂ));
Litex.callOn (Litex.zeroMatrixSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.zeroMatrixInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
  let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
  exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
  let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
  exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))), True.intro⟩)))

theorem h_313 : (by
  let _equal_wd_1_0 := (_object_w19 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w19 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (((show Litex.denote _equal_wd_1_0 = M.number 0 from (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ))))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.zeroMatrixCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)))) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))))] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        ))) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) (_raw_i46 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ))))).mpr ⟨(Litex.callArguments2_mem_cart (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
          let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
          exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
          let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
          exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))), True.intro⟩))).trans (show (M.number 0) = (Litex.denote (Litex.number (M := M) (0 : ℂ))) from rfl)).trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_zero_x5f_matrix_x2f_statement_x2e_lit

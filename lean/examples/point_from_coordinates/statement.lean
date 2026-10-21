import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_point_x5f_from_x5f_coordinates_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.cartCall _value_i1 _ (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.indexSetMemberOfClosedRange (n := 2) (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))));
  let _wd_1_1 := (Litex.cartCall _value_i1 _ (Litex.number (M := M) (2 : ℂ)) h_15 (Litex.indexSetMemberOfClosedRange (n := 2) (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))));
  (let _productChild_0 := _wd_1_0;
  let _productChild_1 := _wd_1_1;
  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
    have _finiteProof_0 := ((Litex.isSet _productChild_0))
    have _finiteProof_1 := ((Litex.isSet _productChild_1))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )))
  exact Litex.Same _value_i1 _object_w2
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_15
    let _object_h16 := (Litex.cartCall _value_i1 _ (Litex.number (M := M) (1 : ℂ)) h_15 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_16 : Litex.In _object_h16 (Litex.R (M := M)) :=
      (Litex.FiniteFunction.coordinate_mem_number h_15 (0 : Fin 2) (1 : ℂ) (by norm_num))
    let _object_h17 := (Litex.cartCall _value_i1 _ (Litex.number (M := M) (2 : ℂ)) h_15 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_17 : Litex.In _object_h17 (Litex.R (M := M)) :=
      (Litex.FiniteFunction.coordinate_mem_number h_15 (1 : Fin 2) (2 : ℂ) (by norm_num))
    let _object_w2 := (let _wd_1_0 := (Litex.cartCall _value_i1 _ (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.indexSetMemberOfClosedRange (n := 2) (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))));
    let _wd_1_1 := (Litex.cartCall _value_i1 _ (Litex.number (M := M) (2 : ℂ)) h_15 (Litex.indexSetMemberOfClosedRange (n := 2) (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))));
    (let _productChild_0 := _wd_1_0;
    let _productChild_1 := _wd_1_1;
    Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
      have _finiteProof_0 := ((Litex.isSet _productChild_0))
      have _finiteProof_1 := ((Litex.isSet _productChild_1))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )))
    have h_1 : Litex.Same _value_i1 _object_w2 :=
      (by
        let _litex_point := _value_i1
        have _litex_member : Litex.In _litex_point (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_15
        have _coordinates : (fun i : Fin 2 => Litex.FunctionSemantics.callValue (M := M) (Litex.denote _litex_point) (Litex.FiniteFunction.index i)) = ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (M.number (2 : ℂ)))] := funext (by
        have _finiteProof_0 := ((show Litex.FunctionSemantics.callValue (M := M) (Litex.denote _litex_point) (Litex.FiniteFunction.index (0 : Fin 2)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (M.number (1 : ℂ))) from by
          have _receiver_equal : (Litex.denote _value_i1) = Litex.denote _litex_point := rfl
          have _index : Litex.FiniteFunction.index (M := M) (0 : Fin 2) = M.number (1 : ℂ) := by norm_num [Litex.FiniteFunction.index]
          simpa only [_index] using (congrArg (fun receiver => Litex.FunctionSemantics.callValue (M := M) receiver (M.number (1 : ℂ))) _receiver_equal).symm
        ))
        have _finiteProof_1 := ((show Litex.FunctionSemantics.callValue (M := M) (Litex.denote _litex_point) (Litex.FiniteFunction.index (1 : Fin 2)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (M.number (2 : ℂ))) from by
          have _receiver_equal : (Litex.denote _value_i1) = Litex.denote _litex_point := rfl
          have _index : Litex.FiniteFunction.index (M := M) (1 : Fin 2) = M.number (2 : ℂ) := by norm_num [Litex.FiniteFunction.index]
          simpa only [_index] using (congrArg (fun receiver => Litex.FunctionSemantics.callValue (M := M) receiver (M.number (2 : ℂ))) _receiver_equal).symm
        ))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )
        have _reconstructed := (Litex.FiniteFunction.reconstruct _litex_member).trans (congrArg (Litex.FiniteFunction.tupleValue (M := M)) _coordinates)
        exact _reconstructed
      )
    exact h_1
  )
end LitexCompiled.file_lean_x2f_examples_x2f_point_x5f_from_x5f_coordinates_x2f_statement_x2e_lit

import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_square_x5f_root_x5f_subexpressions_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : Litex.IsNonempty (Litex.RPos (M := M)) := (Litex.rPosNonempty (M := M))

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M)))

theorem h_3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
  (Litex.inRPos_positive _value_i1 h_2)

theorem h_4 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))

theorem h_5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) _litex_zero.symm)

noncomputable def _object_w2 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) := (let _wd_1_0 := (Litex.sqrt _value_i1 (Litex.inRPos_real _value_i1 h_2) (h_4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (M.real_subset_complex _ (by
    let _litex_sqrt := _atomic_wd_1_0
    exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
  ))) (Litex.numberInC (M := M) (1 : ℂ))))

theorem h_6 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) : (by
  let _atomic_wd_1_0 := (_object_w2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    let _atomic_wd_1_0 := (_object_w2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
    exact (Litex.isSet _atomic_wd_1_0))

noncomputable def _object_w3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) := ((_object_w2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)).val.left

theorem h_54 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) : (by
  let _atomic_wd_1_0 := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    let _atomic_wd_1_0 := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
    exact (Litex.isSet _atomic_wd_1_0))
end LitexCompiled.file_lean_x2f_examples_x2f_square_x5f_root_x5f_subexpressions_x2f_statement_x2e_lit

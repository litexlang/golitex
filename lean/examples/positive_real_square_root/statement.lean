import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_real_x5f_square_x5f_root_x2f_statement_x2e_lit

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

theorem h_6 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
  (h_4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)

noncomputable def _object_w3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) := (let _wd_1_0 := (Litex.sqrt _value_i1 (Litex.inRPos_real _value_i1 h_2) (h_4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
  let _litex_sqrt := _wd_1_0
  exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

theorem h_41 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) : Litex.Same (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) _value_i1 :=
  (by
    let _litex_power := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
    have _litex_nonnegative : Litex.Le (Litex.number (M := M) 0) _litex_power.val.base.val.arg := (h_4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
    have _litex_exponent : Litex.denote _litex_power.val.exponent = M.number ((2 : ℕ) : ℂ) := (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))
    have _litex_square := Litex.sqrtSquareValue _litex_power.val.base.val.arg _litex_power.val.base.wd.1 _litex_nonnegative
    exact (show M.powValue (Litex.denote _litex_power.val.base) (Litex.denote _litex_power.val.exponent) = Litex.denote _litex_power.val.base.val.arg from by
      rw [_litex_exponent]
      exact _litex_square))

theorem h_104 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RPos (M := M))) : Litex.In _value_i1 (Litex.RPos (M := M)) :=
  (by
    have h_96 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) := (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _value_i1 (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (show @Eq M.Value _ _ from Eq.refl _) ((h_41 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)).symm (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))
    have h_101 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
    exact Litex.inOfSame (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) _value_i1 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (h_41 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_96; exact (M.real_members (Litex.denote (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))).mpr ⟨_litex_real, _litex_value⟩) h_96)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_real_x5f_square_x5f_root_x2f_statement_x2e_lit

import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_exponent_x5f_well_x5f_defined_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_1 : Litex.IsNonempty (Litex.Z (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.integer)

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.Z (M := M)))

noncomputable def _object_w2 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.Z (M := M))) := (Litex.powInt (Litex.number (M := M) (2 : ℂ)) _value_i1 (Classical.choose ((M.integer_members (Litex.denote _value_i1)).mp h_2)) (Litex.numberInC (M := M) (2 : ℂ)) h_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote _value_i1)).mp h_2)))

theorem h_3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.Z (M := M))) : (by
  let _equal_wd_1_0 := (_object_w2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
  let _equal_wd_1_1 := _equal_wd_1_0
  exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (show @Eq M.Value _ _ from Eq.refl _)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_exponent_x5f_well_x5f_defined_x2f_statement_x2e_lit

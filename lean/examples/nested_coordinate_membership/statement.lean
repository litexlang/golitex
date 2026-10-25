import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_coordinate_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem _struct_field_checks_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_2 : Litex.In _value_i2 (Litex.R (M := M))), True := by
  intro _Host_i1 _rep_i1 _value_i1 h_1 _Host_i2 _rep_i2 _value_i2 h_2
  exact True.intro

noncomputable def struct_1 : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

noncomputable def _object_w2 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w3 := (struct_1 (M := M))

theorem h_3 : (by
  let _atomic_wd_1_0 := (_object_w2 (M := M))
  let _atomic_wd_1_1 := (_object_w3 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w2 (M := M))
          let _atomic_wd_1_1 := (_object_w3 (M := M))
          exact (Litex.tupleInCart _atomic_wd_1_0 (struct_1 (M := M)) (by
            have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
            have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )))
      )
  )

theorem _struct_field_checks_3 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_6 : Litex.In _value_i5 (_object_w3 (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_7 : Litex.In _value_i6 (Litex.N (M := M))), True := by
  intro _Host_i5 _rep_i5 _value_i5 h_6 _Host_i6 _rep_i6 _value_i6 h_7
  have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalNonnegative _value_i6 h_7)
        )
    )
  exact True.intro

noncomputable def struct_3 : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote (_object_w3 (M := M)), Litex.denote (Litex.N (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (_object_w3 (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.N (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

noncomputable def _object_w6 := (let _wd_1_0 := (_object_w2 (M := M));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
(let _productChild_0 := _wd_1_0;
let _productChild_1 := _wd_1_1;
Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
  have _finiteProof_0 := ((Litex.isSet _productChild_0))
  have _finiteProof_1 := ((Litex.isSet _productChild_1))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)))

noncomputable def _object_w7 := (struct_3 (M := M))

theorem h_9 : (by
  let _atomic_wd_1_0 := (_object_w6 (M := M))
  let _atomic_wd_1_1 := (_object_w7 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w6 (M := M))
          let _atomic_wd_1_1 := (_object_w7 (M := M))
          exact (Litex.tupleInCart _atomic_wd_1_0 (struct_3 (M := M)) (by
            have _finiteProof_0 := ((by
              let _atomic_wd_2_0 := (_object_w2 (M := M))
              let _atomic_wd_2_1 := (_object_w3 (M := M))
              exact (h_3 (M := M))))
            have _finiteProof_1 := ((Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_coordinate_x5f_membership_x2f_statement_x2e_lit

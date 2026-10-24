import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_factorial_x5f_values_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (Litex.factorial (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (let _factorial := _equal_wd_1_0;
        let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
        (Litex.factorialDenoteNat _factorial 0 (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w3 := (Litex.factorial (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num)))

theorem h_4 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) (120 : ℂ) (120 : ℂ) (let _factorial := _equal_wd_1_0;
        let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
        (Litex.factorialDenoteNat _factorial 5 (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (120 : ℂ)) (by norm_num))))
      )
  )

theorem h_8 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_21 : Litex.In _value_i1 (Litex.N (M := M))), (by
  let _object_w7 := (Litex.factorial _value_i1 h_21)
  exact (by
    let _atomic_wd_1_1 := _object_w7
    exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_21
          have h_22 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_21)
                )
            )
          let _object_w7 := (Litex.factorial _value_i1 h_21)
          have h_7 : (by
            let _atomic_wd_1_1 := _object_w7
            exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w7
                    exact (fun _h => (Litex.factorialNonzero _atomic_wd_1_1) _h.symm))
                )
            )
          exact h_7
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_factorial_x5f_values_x2f_statement_x2e_lit

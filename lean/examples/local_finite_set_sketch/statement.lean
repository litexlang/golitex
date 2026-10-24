import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_finite_x5f_set_x5f_sketch_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

include M in
private theorem _sketch_1 : True := by
  let _object_i1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  have h_3 : Litex.Same _object_i1 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
        )
    )
  have h_1 : Litex.In (Litex.number (M := M) (1 : ℂ)) _object_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) _object_i1 (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) ((((Litex.sameRefl _object_i1)).trans h_3)).symm (by
            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (by
              let _set := _atomic_wd_2_1
              exact ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))))
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_finite_x5f_set_x5f_sketch_x2f_statement_x2e_lit

import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_regularity_x5f_singleton_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]
variable [_regularitySemantics : Litex.RegularitySemantics M]

theorem h_3 : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_4 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Same (let _wd_1_0 := _value_i1;
let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.intersect _wd_1_0 _wd_1_1)) (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        (Litex.regularity (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.insertNonempty _atomic_wd_1_0)))
      )
  )

theorem h_7 : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_8 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Same (let _wd_1_0 := _value_i2;
let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.intersect _wd_1_0 _wd_1_1)) (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        (h_3 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_regularity_x5f_singleton_x2f_statement_x2e_lit

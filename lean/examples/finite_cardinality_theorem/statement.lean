import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_cardinality_x5f_theorem_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.IsFiniteSet _value_i1), (by
  let _atomic_wd_1_0 := (Litex.finiteSetSize _value_i1 h_4)
  exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4
          have h_8 : Litex.IsFiniteSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          let _object_w1 := (Litex.finiteSetSize _value_i1 h_8)

          have h_3 : (by
            let _atomic_wd_1_0 := _object_w1
            exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    exact (Litex.finiteSetSizeInN _atomic_wd_1_0))
                )
            )

          have h_13 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _object_w1 h_3)
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w1
            exact h_3)
        )
      )
  )

theorem h_22 : (by
  have h_23 : (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact Litex.IsFiniteSet _atomic_wd_1_0) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (let _finite_tail_0 := _atomic_wd_1_0;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            let _finite_tail_2 := _finite_tail_1.val.tail;
            have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
            have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            _finite_0))
        )
    )
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    (Litex.finiteSetSize _wd_1_0 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact h_23)))
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_23 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.IsFiniteSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_1_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    let _finite_tail_2 := _finite_tail_1.val.tail;
                    have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
                    have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))
                )
            )
          have h_24 : Litex.In (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.finiteSetSize _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact h_23))) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
                    let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
                    let _setTail_2 := Litex.emptySet (M := M);
                    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_23)
                )
            )
          have h_29 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.finiteSetSize _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact h_23))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
                    let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
                    let _setTail_2 := Litex.emptySet (M := M);
                    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.finiteSetSize _wd_1_0 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact h_23))) h_24)
                )
            )
          exact (by
          let _atomic_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.finiteSetSize _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact h_23)))
          exact h_24)
        )
      )
  )

theorem h_35 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.finiteSetSize _wd_1_0 (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0)))) :=
  (by
    litex_complete =>
      exact (
        (Litex.naturalNonnegative (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
          let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.finiteSetSize _wd_1_0 (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (3 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0)))) (h_22 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_cardinality_x5f_theorem_x2f_statement_x2e_lit

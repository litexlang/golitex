import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_family_x5f_intersection_x5f_member_x2f_statement_x2e_lit

universe u v1 v2 v3 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]
variable [_indexedUnionSemantics : Litex.IndexedUnionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsNonempty _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.IsSet _value_i2) (h_2 : ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_7 : Litex.In _value_i3 _value_i1), Litex.In _value_i2 _value_i3), (by
  let _atomic_wd_1_1 := (Litex.familyIntersect _value_i1 h_5)
  exact Litex.In _value_i2 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 h_2
          have h_12 : Litex.IsNonempty _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_13 : Litex.IsSet _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_16 : Litex.In _value_i2 (Litex.familyIntersect _value_i1 h_12) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_17 : Litex.IsSet _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.isSet _value_i1)
                          )
                      )
                    have h_18 : Litex.IsNonempty _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_12
                          )
                      )
                    have h_23 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_43 : Litex.In _value_i6 _value_i1), Litex.IsSet _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i6 _rep_i6 _value_i6 h_43
                              have h_22 : Litex.IsSet _value_i6 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.isSet _value_i6)
                                    )
                                )
                              exact h_22
                            )
                          )
                      )
                    have h_21 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_64 : Litex.In _value_i5 _value_i1) (h_19 : Litex.IsSet _value_i5), Litex.In _value_i2 _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i5 _rep_i5 _value_i5 h_64 h_19
                              have h_20 : Litex.In _value_i2 _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        have h_73 : Litex.In _value_i5 _value_i1 :=
                                          h_64
                                        exact (Litex.inOfSame _value_i2 _value_i2 _value_i5 _value_i5 (Litex.sameRefl _value_i2) (Litex.sameRefl _value_i5) (h_2 _value_i5 h_73))
                                      )
                                    )
                                )
                              exact h_20
                            )
                          )
                      )
                    exact (Litex.familyIntersectMember (Litex.familyIntersect _value_i1 h_18) _value_i2 (Litex.forallMembersOfRepresentations _value_i1 (fun _factor _hi => h_21 _factor _hi (Litex.isSet _factor))))
                  )
                )
            )
          exact (by
            let _atomic_wd_1_1 := (Litex.familyIntersect _value_i1 h_12)
            exact h_16)
        )
      )
  )

noncomputable def _object_w2 := (Litex.familyIntersect (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0);
(let _setElement_0 := _wd_1_0;
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)) (by
  let _atomic_wd_1_0 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0);
  (let _setElement_0 := _wd_1_0;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (Litex.insertNonempty _atomic_wd_1_0)))

theorem h_95 : (by
  let _atomic_wd_1_0 := (_object_w2 (M := M))
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w2 (M := M))
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )

theorem h_98 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_111 : Litex.In _value_i7 (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(let _setElement_0 := _wd_1_0;
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0))), Litex.In (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_111
          have h_112 : Litex.Same _value_i7 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote _value_i7) (Litex.SetSemantics.insertValue (Litex.denote (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0)) (Litex.SetSemantics.emptyValue (M := M))) := h_111
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_97 : Litex.In (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) _value_i7 (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) ((((Litex.sameRefl _value_i7)).trans h_112)).symm (by
                    let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (by
                      let _set := _atomic_wd_2_1
                      exact ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))))
                )
            )
          exact h_97
        )
      )
  )

theorem h_126 : (by
  have h_127 : (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    (let _setElement_0 := _wd_1_0;
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0))
    exact Litex.IsNonempty _atomic_wd_1_0) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (let _setElement_0 := _wd_1_0;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact (Litex.insertNonempty _atomic_wd_1_0))
        )
    )
  exact (by
    let _atomic_wd_1_1 := (Litex.familyIntersect (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    (let _setElement_0 := _wd_1_0;
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)) (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
        let _setTail_1 := Litex.emptySet (M := M);
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0);
      (let _setElement_0 := _wd_1_0;
        let _setTail_1 := Litex.emptySet (M := M);
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0))
      exact h_127))
    exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_127 : (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (let _setElement_0 := _wd_1_0;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact Litex.IsNonempty _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (let _setElement_0 := _wd_1_0;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0))
                    exact (Litex.insertNonempty _atomic_wd_1_0))
                )
            )
          have h_128 : Litex.IsSet (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.number (M := M) (1 : ℂ)))
                )
            )
          have h_130 : ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_137 : Litex.In _value_i3 (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (let _setElement_0 := _wd_1_0;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))), Litex.In (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i3 _rep_i3 _value_i3 h_137
                    have h_138 : Litex.Same _value_i3 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              have _member : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (Litex.denote (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0)) (Litex.SetSemantics.emptyValue (M := M))) := h_137
                              exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                          )
                      )
                    exact ((h_98 (M := M)) _value_i3 h_137)
                  )
                )
            )
          have h_131 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.familyIntersect (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (let _setElement_0 := _wd_1_0;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)) (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (let _setElement_0 := _wd_1_0;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact h_127)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_4 (M := M)) (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (let _setElement_0 := _wd_1_0;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0)) h_127 (Litex.number (M := M) (1 : ℂ)) h_128 h_130)
                )
            )
          exact (by
          let _atomic_wd_1_1 := (Litex.familyIntersect (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (let _setElement_0 := _wd_1_0;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)) (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (let _setElement_0 := _wd_1_0;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact h_127))
          exact h_131)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_family_x5f_intersection_x5f_member_x2f_statement_x2e_lit

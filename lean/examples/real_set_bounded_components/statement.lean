import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_set_x5f_bounded_x5f_components_x2f_statement_x2e_lit

universe u v1 v7 v12
variable {M : Litex.Semantics.{u}}

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.IsSet _value_i1) (h_1 : Litex.Subset _value_i1 (Litex.R (M := M))) (h_2 : Litex.RealBounded _value_i1), ((Litex.RealBoundedAbove _value_i1) ∧ (Litex.RealBoundedBelow _value_i1)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 h_1 h_2
          have h_16 : (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.denote _value_i1) (Litex.denote _value_i3))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_2).1
                )
            )
          have h_18 : (∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.denote _value_i1) (Litex.denote _value_i4))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_2).2
                )
            )
          have h_19 : (Litex.RealBoundedAboveValue M (Litex.denote _value_i1)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_2).2
                )
            )
          have h_20 : (Litex.RealBoundedBelowValue M (Litex.denote _value_i1)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_2).1
                )
            )
          have h_3 : Litex.RealBoundedAbove _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_19
                )
            )
          have h_24 : (∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i5) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.denote _value_i1) (Litex.denote _value_i5))) :=
            (by
              litex_checked_step =>
                exact (
                  h_3
                )
            )
          have h_4 : Litex.RealBoundedBelow _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_20
                )
            )
          have h_28 : (∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i6) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.denote _value_i1) (Litex.denote _value_i6))) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          exact (And.intro h_3 h_4)
        )
      )
  )

theorem h_33 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_34 : Litex.IsSet _value_i7) (h_29 : Litex.Subset _value_i7 (Litex.R (M := M))) (h_30 : Litex.RealBoundedAbove _value_i7), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_45 : Litex.In _value_i8 (Litex.R (M := M))), Litex.RealUpperBound _value_i7 _value_i8 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_34 h_29 h_30
          have h_44 : (∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.denote _value_i7) (Litex.denote _value_i10))) :=
            (by
              litex_checked_step =>
                exact (
                  h_30
                )
            )
          have h_32 : ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_45 : Litex.In _value_i8 (Litex.R (M := M))), Litex.RealUpperBound _value_i7 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  h_44
                )
            )
          exact h_32
        )
      )
  )

theorem h_62 : ∀ {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_65 : Litex.IsSet _value_i12) (h_58 : Litex.Subset _value_i12 (Litex.R (M := M))) (h_59 : Litex.RealBoundedBelow _value_i12), ∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (h_76 : Litex.In _value_i13 (Litex.R (M := M))), Litex.RealLowerBound _value_i12 _value_i13 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i12 _rep_i12 _value_i12 h_65 h_58 h_59
          have h_75 : (∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.denote _value_i12) (Litex.denote _value_i15))) :=
            (by
              litex_checked_step =>
                exact (
                  h_59
                )
            )
          have h_61 : ∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (h_76 : Litex.In _value_i13 (Litex.R (M := M))), Litex.RealLowerBound _value_i12 _value_i13 :=
            (by
              litex_checked_step =>
                exact (
                  h_75
                )
            )
          exact h_61
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_set_x5f_bounded_x5f_components_x2f_statement_x2e_lit

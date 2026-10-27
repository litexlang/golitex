import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_set_x5f_bound_x5f_citations_x2f_statement_x2e_lit

universe u v1 v2 v6 v7 v9 v10 v14 v15 v17 v21 v23 v27 v29 v35
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : Litex.Subset _value_i1 (Litex.R (M := M))) (h_2 : Litex.RealUpperBound _value_i1 _value_i2), Litex.RealUpperBound _value_i1 _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 h_1 h_2
          have h_33 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i4 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i4 _value_i1), (∃ (_r _s : ℝ), (Litex.denote _value_i4) = M.number (_r : ℂ) ∧ (Litex.denote _value_i2) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i4 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i4 _value_i1) => (h_2) (Litex.denote _value_i4) _member)
                )
            )
          have h_3 : Litex.RealUpperBound _value_i1 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_2
                )
            )
          have h_39 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i5 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i5 _value_i1), (∃ (_r _s : ℝ), (Litex.denote _value_i5) = M.number (_r : ℂ) ∧ (Litex.denote _value_i2) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i5 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i5 _value_i1) => (h_3) (Litex.denote _value_i5) _member)
                )
            )
          exact h_3
        )
      )
  )

theorem h_43 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_58 : Litex.IsSet _value_i6) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_59 : Litex.In _value_i7 (Litex.R (M := M))) (h_40 : Litex.Subset _value_i6 (Litex.R (M := M))) (h_41 : ¬ (Litex.RealUpperBound _value_i6 _value_i7)), ¬ (Litex.RealUpperBound _value_i6 _value_i7) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_58 _Host_i7 _rep_i7 _value_i7 h_59 h_40 h_41
          have h_42 : ¬ (Litex.RealUpperBound _value_i6 _value_i7) :=
            (by
              litex_checked_step =>
                exact (
                  h_41
                )
            )
          exact h_42
        )
      )
  )

theorem h_80 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_97 : Litex.IsSet _value_i9) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_98 : Litex.In _value_i10 (Litex.R (M := M))) (h_77 : Litex.Subset _value_i9 (Litex.R (M := M))) (h_78 : Litex.RealLowerBound _value_i9 _value_i10), Litex.RealLowerBound _value_i9 _value_i10 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_97 _Host_i10 _rep_i10 _value_i10 h_98 h_77 h_78
          have h_113 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i12 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i12 _value_i9), (∃ (_r _s : ℝ), (Litex.denote _value_i10) = M.number (_r : ℂ) ∧ (Litex.denote _value_i12) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i12 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i12 _value_i9) => (h_78) (Litex.denote _value_i12) _member)
                )
            )
          have h_79 : Litex.RealLowerBound _value_i9 _value_i10 :=
            (by
              litex_checked_step =>
                exact (
                  h_78
                )
            )
          have h_119 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i13 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i13 _value_i9), (∃ (_r _s : ℝ), (Litex.denote _value_i10) = M.number (_r : ℂ) ∧ (Litex.denote _value_i13) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i13 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i13 _value_i9) => (h_79) (Litex.denote _value_i13) _member)
                )
            )
          exact h_79
        )
      )
  )

theorem h_123 : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_142 : Litex.IsSet _value_i14) {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_143 : Litex.In _value_i15 (Litex.R (M := M))) (h_120 : Litex.Subset _value_i14 (Litex.R (M := M))) (h_121 : ¬ (Litex.RealLowerBound _value_i14 _value_i15)), ¬ (Litex.RealLowerBound _value_i14 _value_i15) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 h_142 _Host_i15 _rep_i15 _value_i15 h_143 h_120 h_121
          have h_122 : ¬ (Litex.RealLowerBound _value_i14 _value_i15) :=
            (by
              litex_checked_step =>
                exact (
                  h_121
                )
            )
          exact h_122
        )
      )
  )

theorem h_164 : ∀ {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_165 : Litex.IsSet _value_i17) (h_161 : Litex.Subset _value_i17 (Litex.R (M := M))) (h_162 : Litex.RealBoundedAbove _value_i17), Litex.RealBoundedAbove _value_i17 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i17 _rep_i17 _value_i17 h_165 h_161 h_162
          have h_175 : (∃ (_value_i19 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.denote _value_i17) (Litex.denote _value_i19))) :=
            (by
              litex_checked_step =>
                exact (
                  h_162
                )
            )
          have h_163 : Litex.RealBoundedAbove _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  h_162
                )
            )
          have h_179 : (∃ (_value_i20 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i20) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.denote _value_i17) (Litex.denote _value_i20))) :=
            (by
              litex_checked_step =>
                exact (
                  h_163
                )
            )
          exact h_163
        )
      )
  )

theorem h_183 : ∀ {_Host_i21 : Type v21} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_186 : Litex.IsSet _value_i21) (h_180 : Litex.Subset _value_i21 (Litex.R (M := M))) (h_181 : ¬ (Litex.RealBoundedAbove _value_i21)), ¬ (Litex.RealBoundedAbove _value_i21) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i21 _rep_i21 _value_i21 h_186 h_180 h_181
          have h_182 : ¬ (Litex.RealBoundedAbove _value_i21) :=
            (by
              litex_checked_step =>
                exact (
                  h_181
                )
            )
          exact h_182
        )
      )
  )

theorem h_200 : ∀ {_Host_i23 : Type v23} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (h_205 : Litex.IsSet _value_i23) (h_197 : Litex.Subset _value_i23 (Litex.R (M := M))) (h_198 : Litex.RealBoundedBelow _value_i23), Litex.RealBoundedBelow _value_i23 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i23 _rep_i23 _value_i23 h_205 h_197 h_198
          have h_215 : (∃ (_value_i25 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i25) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.denote _value_i23) (Litex.denote _value_i25))) :=
            (by
              litex_checked_step =>
                exact (
                  h_198
                )
            )
          have h_199 : Litex.RealBoundedBelow _value_i23 :=
            (by
              litex_checked_step =>
                exact (
                  h_198
                )
            )
          have h_219 : (∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i26) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.denote _value_i23) (Litex.denote _value_i26))) :=
            (by
              litex_checked_step =>
                exact (
                  h_199
                )
            )
          exact h_199
        )
      )
  )

theorem h_223 : ∀ {_Host_i27 : Type v27} [_rep_i27 : Litex.Representation M _Host_i27] (_value_i27 : Litex.Obj (M := M) _Host_i27) (h_230 : Litex.IsSet _value_i27) (h_220 : Litex.Subset _value_i27 (Litex.R (M := M))) (h_221 : ¬ (Litex.RealBoundedBelow _value_i27)), ¬ (Litex.RealBoundedBelow _value_i27) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i27 _rep_i27 _value_i27 h_230 h_220 h_221
          have h_222 : ¬ (Litex.RealBoundedBelow _value_i27) :=
            (by
              litex_checked_step =>
                exact (
                  h_221
                )
            )
          exact h_222
        )
      )
  )

theorem h_244 : ∀ {_Host_i29 : Type v29} [_rep_i29 : Litex.Representation M _Host_i29] (_value_i29 : Litex.Obj (M := M) _Host_i29) (h_253 : Litex.IsSet _value_i29) (h_241 : Litex.Subset _value_i29 (Litex.R (M := M))) (h_242 : Litex.RealBounded _value_i29), Litex.RealBounded _value_i29 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i29 _rep_i29 _value_i29 h_253 h_241 h_242
          have h_263 : (∃ (_value_i31 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i31) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.denote _value_i29) (Litex.denote _value_i31))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_242).1
                )
            )
          have h_265 : (∃ (_value_i32 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i32) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.denote _value_i29) (Litex.denote _value_i32))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_242).2
                )
            )
          have h_266 : (Litex.RealBoundedAboveValue M (Litex.denote _value_i29)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_242).2
                )
            )
          have h_267 : (Litex.RealBoundedBelowValue M (Litex.denote _value_i29)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_242).1
                )
            )
          have h_243 : Litex.RealBounded _value_i29 :=
            (by
              litex_checked_step =>
                exact (
                  h_242
                )
            )
          have h_271 : (∃ (_value_i33 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i33) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.denote _value_i29) (Litex.denote _value_i33))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_243).1
                )
            )
          have h_273 : (∃ (_value_i34 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i34) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.denote _value_i29) (Litex.denote _value_i34))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_243).2
                )
            )
          have h_274 : (Litex.RealBoundedAboveValue M (Litex.denote _value_i29)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_243).2
                )
            )
          have h_275 : (Litex.RealBoundedBelowValue M (Litex.denote _value_i29)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_243).1
                )
            )
          exact h_243
        )
      )
  )

theorem h_279 : ∀ {_Host_i35 : Type v35} [_rep_i35 : Litex.Representation M _Host_i35] (_value_i35 : Litex.Obj (M := M) _Host_i35) (h_290 : Litex.IsSet _value_i35) (h_276 : Litex.Subset _value_i35 (Litex.R (M := M))) (h_277 : ¬ (Litex.RealBounded _value_i35)), ¬ (Litex.RealBounded _value_i35) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i35 _rep_i35 _value_i35 h_290 h_276 h_277
          have h_278 : ¬ (Litex.RealBounded _value_i35) :=
            (by
              litex_checked_step =>
                exact (
                  h_277
                )
            )
          exact h_278
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_set_x5f_bound_x5f_citations_x2f_statement_x2e_lit

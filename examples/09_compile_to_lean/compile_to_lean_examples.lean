import Litex.Rules

namespace __Sketch01

theorem __fact43 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (b : Litex.Object) (__h0_2 : Litex.In b Litex.R) (g : Litex.Object) (__h0_3 : Litex.In g (Litex.fnSpace1 Litex.R Litex.R)) (t : Litex.Object) (__h0_4 : Litex.In t (Litex.fnSpace1 Litex.R Litex.R)) (f : Litex.Object) (__h0_5 : Litex.In f (Litex.fnSpace2 Litex.R Litex.R Litex.R)), (f [(g [a]), (t [b])]) = (f [(g [a]), (t [b])]) :=
by
  intro a __h0_1 b __h0_2 g __h0_3 t __h0_4 f __h0_5
  have __wd0_7 : Litex.In a Litex.R := by
    exact (__h0_1)
  have __obj44_app : Litex.Applicable (g) [a] := by
    exact (Litex.fnSpaceApplicable (args := [a]) __h0_3 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, True
      exact Exists.intro (__wd0_7) (True.intro)))
  have __obj44_result : Litex.In (g [a]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [a]) __h0_3 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, True
      exact Exists.intro (__wd0_7) (True.intro))))
  have __wd0_8 : Litex.In b Litex.R := by
    exact (__h0_2)
  have __obj45_app : Litex.Applicable (t) [b] := by
    exact (Litex.fnSpaceApplicable (args := [b]) __h0_4 rfl (by
      change ∃ __h_arg0 : Litex.In (b) Litex.R, True
      exact Exists.intro (__wd0_8) (True.intro)))
  have __obj45_result : Litex.In (t [b]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [b]) __h0_4 rfl (by
      change ∃ __h_arg0 : Litex.In (b) Litex.R, True
      exact Exists.intro (__wd0_8) (True.intro))))
  have __wd0_9 : Litex.In g (Litex.fnSpace1 Litex.R Litex.R) := by
    exact (__h0_3)
  have __wd0_10 : Litex.In (g [a]) Litex.R := by
    exact ((by simpa using (Litex.fnSpaceResult (args := [a]) __h0_3 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, True
      exact Exists.intro (__wd0_7) (True.intro)))))
  have __wd0_11 : Litex.In t (Litex.fnSpace1 Litex.R Litex.R) := by
    exact (__h0_4)
  have __wd0_12 : Litex.In (t [b]) Litex.R := by
    exact ((by simpa using (Litex.fnSpaceResult (args := [b]) __h0_4 rfl (by
      change ∃ __h_arg0 : Litex.In (b) Litex.R, True
      exact Exists.intro (__wd0_8) (True.intro)))))
  have __obj46_app : Litex.Applicable (f) [(g [a]), (t [b])] := by
    exact (Litex.fnSpaceApplicable (args := [(g [a]), (t [b])]) __h0_5 rfl (by
      change ∃ __h_arg0 : Litex.In ((g [a])) Litex.R, ∃ __h_arg1 : Litex.In ((t [b])) Litex.R, True
      exact Exists.intro (__wd0_10) (Exists.intro (__wd0_12) (True.intro))))
  have __obj46_result : Litex.In (f [(g [a]), (t [b])]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [(g [a]), (t [b])]) __h0_5 rfl (by
      change ∃ __h_arg0 : Litex.In ((g [a])) Litex.R, ∃ __h_arg1 : Litex.In ((t [b])) Litex.R, True
      exact Exists.intro (__wd0_10) (Exists.intro (__wd0_12) (True.intro)))))
  exact rfl

end __Sketch01

namespace __Sketch02

axiom p : Litex.Object → Prop

axiom __fact46 : ∀ (x : Litex.Object) (__h0_1 : Litex.In x Litex.R), p x

theorem __fact47 : p 1 := by
  exact (__fact46 1 (Litex.Rules.numeralInR 1))

end __Sketch02

namespace __Sketch03

theorem __fact60 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (b : Litex.Object) (__h0_2 : Litex.In b Litex.C) (c : Litex.Object) (__h0_3 : Litex.In c Litex.C), (Litex.add (Litex.add a b) c) = (Litex.add (Litex.add a b) c) :=
by
  intro a __h0_1 b __h0_2 c __h0_3
  have __wd0_23 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __wd0_24 : Litex.In b Litex.C := by
    exact (__h0_2)
  have __wd0_25 : Litex.In (Litex.add a b) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_23) (__wd0_24)))
  have __wd0_26 : Litex.In c Litex.C := by
    exact (__h0_3)
  have __obj84_result : Litex.In (Litex.add (Litex.add a b) c) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_25) (__wd0_26)))
  exact rfl

theorem __fact73 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (b : Litex.Object) (__h0_2 : Litex.In b Litex.C) (c : Litex.Object) (__h0_3 : Litex.In c Litex.C), (Litex.add (Litex.mul (Litex.sub a b) c) a) = (Litex.add (Litex.mul (Litex.sub a b) c) a) :=
by
  intro a __h0_1 b __h0_2 c __h0_3
  have __wd0_37 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __wd0_38 : Litex.In b Litex.C := by
    exact (__h0_2)
  have __wd0_39 : Litex.In (Litex.sub a b) Litex.C := by
    exact ((Litex.Rules.complexSubClosure (__wd0_37) (__wd0_38)))
  have __wd0_40 : Litex.In c Litex.C := by
    exact (__h0_3)
  have __wd0_41 : Litex.In (Litex.mul (Litex.sub a b) c) Litex.C := by
    exact ((Litex.Rules.complexMulClosure (__wd0_39) (__wd0_40)))
  have __wd0_42 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __obj104_result : Litex.In (Litex.add (Litex.mul (Litex.sub a b) c) a) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_41) (__wd0_42)))
  exact rfl

theorem __fact86 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (b : Litex.Object) (__h0_2 : Litex.In b Litex.C) (__h0_3 : b ≠ 0), (Litex.div a b) = (Litex.div a b) :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_52 : b ≠ 0 := by
    exact (__h0_3)
  have __wd0_53 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __wd0_54 : Litex.In b Litex.C := by
    exact (__h0_2)
  have __obj121_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_53) (__wd0_54) (__wd0_52)))
  exact rfl

theorem __fact99 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (b : Litex.Object) (__h0_2 : Litex.In b Litex.C) (__h0_3 : b ≠ 0), (Litex.add (Litex.div a b) a) = (Litex.add (Litex.div a b) a) :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_63 : b ≠ 0 := by
    exact (__h0_3)
  have __wd0_64 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __wd0_65 : Litex.In b Litex.C := by
    exact (__h0_2)
  have __wd0_66 : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_64) (__wd0_65) (__wd0_63)))
  have __wd0_67 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __obj138_result : Litex.In (Litex.add (Litex.div a b) a) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_66) (__wd0_67)))
  exact rfl

theorem __fact112 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (b : Litex.Object) (__h0_2 : Litex.In b Litex.R) (__h0_3 : b ≠ 0), Litex.In (Litex.div a b) Litex.R :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_78 : b ≠ 0 := by
    exact (__h0_3)
  have __wd0_79 : Litex.In a Litex.R := by
    exact (__h0_1)
  have __wd0_80 : Litex.In a Litex.C := by
    exact ((Litex.Rules.realInComplex (__h0_1)))
  have __wd0_81 : Litex.In b Litex.R := by
    exact (__h0_2)
  have __wd0_82 : Litex.In b Litex.C := by
    exact ((Litex.Rules.realInComplex (__h0_2)))
  have __obj156_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_80) (__wd0_82) (__wd0_78)))
  exact (Litex.Rules.realDivClosure (__wd0_80) (__wd0_82) (__wd0_78) (__h0_1) (__h0_2))

end __Sketch03

namespace __Sketch04

theorem __fact128 : ∀ (x : Litex.Object) (__h0_1 : Litex.In x Litex.RPos), Litex.Lt 0 x :=
by
  intro x __h0_1
  have __inferred0 : Litex.Lt 0 x := by
    exact (Litex.Rules.positiveRealMembership __h0_1)
  exact __inferred0

end __Sketch04

namespace __Sketch05

theorem __fact141 : ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a) (b : Litex.Object) (__h0_2 : Litex.IsSet b) (__h0_3 : a ≠ b), (Litex.listSet [a, b]) = (Litex.listSet [a, b]) :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_98 : a ≠ b := by
    exact (__h0_3)
  exact rfl

theorem __fact163 : ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a) (b : Litex.Object) (__h0_2 : Litex.IsSet b) (c : Litex.Object) (__h0_3 : Litex.IsSet c) (__h0_4 : a ≠ b) (__h0_5 : a ≠ c) (__h0_6 : b ≠ c), (Litex.listSet [a, b, c]) = (Litex.listSet [a, b, c]) :=
by
  intro a __h0_1 b __h0_2 c __h0_3 __h0_4 __h0_5 __h0_6
  have __wd0_103 : a ≠ b := by
    exact (__h0_4)
  have __wd0_104 : a ≠ c := by
    exact (__h0_5)
  have __wd0_105 : b ≠ c := by
    exact (__h0_6)
  exact rfl

end __Sketch05

namespace __Sketch06

noncomputable def x : Litex.Object := Classical.choose (Litex.Rules.realSetNonempty)

theorem __fact166 : Litex.In x Litex.R := by
  unfold x
  exact Classical.choose_spec (Litex.Rules.realSetNonempty)

end __Sketch06

namespace __Sketch07

theorem __fact174 : ∃ (x : Litex.Object), Litex.In x Litex.R ∧ x = 1 := by
  exact (by
  have __exist_step1 : (1 : Litex.Object) = 1 := by
    exact rfl
  exact ⟨1, (Litex.Rules.numeralInR 1), (__exist_step1)⟩)

noncomputable def y : Litex.Object := Classical.choose (__fact174)

theorem __fact179 : Litex.In y Litex.R := by
  unfold y
  exact (Classical.choose_spec (__fact174)).1

theorem __fact180 : y = 1 := by
  unfold y
  exact (Classical.choose_spec (__fact174)).2

end __Sketch07

namespace __Sketch08

theorem __fact183 : (1 : Litex.Object) = 1 := by
  exact (by
  have __case1 : (1 : Litex.Object) = 1 := rfl
  have __case1_step_1 : (2 : Litex.Object) = 2 := by
    exact (rfl)
  exact __case1)

theorem __fact185 : (2 : Litex.Object) = 2 := by
  exact (by
  classical
  by_contra __reverse
  have __contra_step_1 : (1 : Litex.Object) = 1 := by
    exact (rfl)
  exact ((__reverse) : (2 : Litex.Object) ≠ 2) (rfl))

theorem __fact189 : (4 : Litex.Object) = 4 := by
  exact (by
  have __case1 : (3 : Litex.Object) = 3 ∧ ((4 : Litex.Object) = 4) := And.intro (rfl) ((rfl))
  have __case1_step_1 : (3 : Litex.Object) = 3 := by
    exact (((__case1)).1)
  have __case1_step_2 : (4 : Litex.Object) = 4 := by
    exact (((__case1)).2)
  have __case1_step_3 : (3 : Litex.Object) = 3 := by
    exact (rfl)
  exact __case1_step_2)

theorem __fact191 : (5 : Litex.Object) ≠ 6 := by
  exact (by
  classical
  exact Classical.byContradiction (fun __negated_goal => by
    have __reverse : (5 : Litex.Object) = 6 := Classical.byContradiction (fun __not_reverse => __negated_goal __not_reverse)
    exact (((by
  exact (Litex.Rules.numeralNe 5 6).2 (by norm_num))) : (5 : Litex.Object) ≠ 6) (__reverse)))

end __Sketch08

namespace __Sketch09

theorem one_eq_one : (1 : Litex.Object) = 1 :=
by
  exact rfl

end __Sketch09

namespace __Sketch10

theorem __fact194 : Litex.pi = Litex.pi := by
  exact rfl

theorem __fact204 : ∀ (A : Litex.Object) (__h0_1 : Litex.IsSet A) (B : Litex.Object) (__h0_2 : Litex.IsSet B), (Litex.union A B) = (Litex.union A B) :=
by
  intro A __h0_1 B __h0_2
  exact rfl

end __Sketch10

namespace __Sketch11

theorem __fact217 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (b : Litex.Object) (__h0_2 : Litex.In b Litex.C) (__h0_3 : b ≠ 0), (Litex.div a b) = (Litex.div a b) :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_112 : b ≠ 0 := by
    exact (__h0_3)
  have __wd0_113 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __wd0_114 : Litex.In b Litex.C := by
    exact (__h0_2)
  have __obj255_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_113) (__wd0_114) (__wd0_112)))
  exact rfl

theorem __fact230 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (b : Litex.Object) (__h0_2 : Litex.In b Litex.R) (__h0_3 : b ≠ 0), Litex.In (Litex.div a b) Litex.R :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_123 : b ≠ 0 := by
    exact (__h0_3)
  have __wd0_124 : Litex.In a Litex.R := by
    exact (__h0_1)
  have __wd0_125 : Litex.In a Litex.C := by
    exact ((Litex.Rules.realInComplex (__h0_1)))
  have __wd0_126 : Litex.In b Litex.R := by
    exact (__h0_2)
  have __wd0_127 : Litex.In b Litex.C := by
    exact ((Litex.Rules.realInComplex (__h0_2)))
  have __obj272_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_125) (__wd0_127) (__wd0_123)))
  exact (Litex.Rules.realDivClosure (__wd0_125) (__wd0_127) (__wd0_123) (__h0_1) (__h0_2))

end __Sketch11

namespace __Sketch12

noncomputable def S : Litex.Object := (Litex.setBuilder Litex.R (fun __x73 => __x73 = __x73))

theorem __fact234 : Litex.IsSet S := by
  simpa only [S] using (Litex.Rules.objectIsSet (Litex.setBuilder Litex.R (fun __x73 => __x73 = __x73)))

theorem __fact235 : S = (Litex.setBuilder Litex.R (fun __x73 => __x73 = __x73)) := by
  rfl

theorem __fact236 : S = S := by
  exact rfl

end __Sketch12

namespace __Sketch13

noncomputable def __litex_id_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)

noncomputable def __litex_id_body
    (__fn_arg : List Litex.Object)
    (__fn_arg_len : __fn_arg.length = __litex_id_spec.arity)
    (__fn_arg_req : __litex_id_spec.requirements __fn_arg) : Litex.Object :=
  (Litex.arg __fn_arg 0)

theorem __litex_id_closed :
    ∀ __fn_arg __fn_arg_len __fn_arg_req,
      Litex.In
        (__litex_id_body __fn_arg __fn_arg_len __fn_arg_req)
        (__litex_id_spec.range __fn_arg __fn_arg_len __fn_arg_req) := by
  intro __fn_arg __fn_arg_len __fn_arg_req
  change Litex.In (Litex.arg __fn_arg 0) Litex.R
  exact Exists.choose (__fn_arg_req)

noncomputable def __litex_id_impl : Litex.Object :=
  Litex.functionObject __litex_id_spec __litex_id_body

noncomputable def litex_id : Litex.Object := __litex_id_impl

theorem __fact241 : Litex.In litex_id (Litex.FnSet ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)) := by
  simpa only [litex_id, __litex_id_impl, __litex_id_spec] using
    (Litex.functionObjectInFnSet __litex_id_spec __litex_id_body __litex_id_closed)

theorem __fact242 : litex_id = __litex_id_impl := by
  rfl

theorem __fact243 : (litex_id [1]) = 1 := by
  have __wd0_134 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have __obj298_app : Litex.Applicable (litex_id) [1] := by
    exact (Litex.fnSetApplicable (args := [1]) __fact241 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_134) (True.intro)))
  have __obj298_result : Litex.In (litex_id [1]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult (args := [1]) __fact241 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_134) (True.intro))))
  exact (by
  change ((litex_id) [1]) = 1
  rw [__fact242]
  unfold __litex_id_impl
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [__fact242, __litex_id_impl] using __obj298_app)]
  simp only [__litex_id_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

noncomputable def __inc_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)

noncomputable def __inc_body
    (__fn_arg : List Litex.Object)
    (__fn_arg_len : __fn_arg.length = __inc_spec.arity)
    (__fn_arg_req : __inc_spec.requirements __fn_arg) : Litex.Object :=
  (Litex.add (Litex.arg __fn_arg 0) 1)

theorem __inc_closed :
    ∀ __fn_arg __fn_arg_len __fn_arg_req,
      Litex.In
        (__inc_body __fn_arg __fn_arg_len __fn_arg_req)
        (__inc_spec.range __fn_arg __fn_arg_len __fn_arg_req) := by
  intro __fn_arg __fn_arg_len __fn_arg_req
  have __wd0_140 : Litex.In (Litex.arg __fn_arg 0) Litex.R := by
    exact (Exists.choose (__fn_arg_req))
  have __wd0_141 : Litex.In (Litex.arg __fn_arg 0) Litex.C := by
    exact ((Litex.Rules.realInComplex (Exists.choose (__fn_arg_req))))
  have __wd0_142 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __obj307_result : Litex.In (Litex.add (Litex.arg __fn_arg 0) 1) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_141) (__wd0_142)))
  change Litex.In (Litex.add (Litex.arg __fn_arg 0) 1) Litex.R
  exact (Litex.Rules.realAddClosure (__wd0_141) (__wd0_142) (Exists.choose (__fn_arg_req)) (Litex.Rules.numeralInR 1))

noncomputable def __inc_impl : Litex.Object :=
  Litex.functionObject __inc_spec __inc_body

noncomputable def inc : Litex.Object := __inc_impl

theorem __fact248 : Litex.In inc (Litex.FnSet ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)) := by
  simpa only [inc, __inc_impl, __inc_spec] using
    (Litex.functionObjectInFnSet __inc_spec __inc_body __inc_closed)

theorem __fact249 : inc = __inc_impl := by
  rfl

theorem __fact250 : (inc [1]) = (Litex.add 1 1) := by
  have __wd0_143 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have __obj311_app : Litex.Applicable (inc) [1] := by
    exact (Litex.fnSetApplicable (args := [1]) __fact248 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_143) (True.intro)))
  have __obj311_result : Litex.In (inc [1]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult (args := [1]) __fact248 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_143) (True.intro))))
  have __wd0_144 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __obj313_result : Litex.In (Litex.add 1 1) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_144) (__wd0_144)))
  exact (by
  change ((inc) [1]) = (Litex.add 1 1)
  rw [__fact249]
  unfold __inc_impl
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [__fact249, __inc_impl] using __obj311_app)]
  simp only [__inc_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

noncomputable def __reciprocal_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, ∃ __h_dom0 : (Litex.arg __fn_arg 0) ≠ 0, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)

noncomputable def __reciprocal_body
    (__fn_arg : List Litex.Object)
    (__fn_arg_len : __fn_arg.length = __reciprocal_spec.arity)
    (__fn_arg_req : __reciprocal_spec.requirements __fn_arg) : Litex.Object :=
  (Litex.div 1 (Litex.arg __fn_arg 0))

theorem __reciprocal_closed :
    ∀ __fn_arg __fn_arg_len __fn_arg_req,
      Litex.In
        (__reciprocal_body __fn_arg __fn_arg_len __fn_arg_req)
        (__reciprocal_spec.range __fn_arg __fn_arg_len __fn_arg_req) := by
  intro __fn_arg __fn_arg_len __fn_arg_req
  have __wd0_151 : (Litex.arg __fn_arg 0) ≠ 0 := by
    exact (Exists.choose (Exists.choose_spec (__fn_arg_req)))
  have __wd0_152 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __wd0_153 : Litex.In (Litex.arg __fn_arg 0) Litex.R := by
    exact (Exists.choose (__fn_arg_req))
  have __wd0_154 : Litex.In (Litex.arg __fn_arg 0) Litex.C := by
    exact ((Litex.Rules.realInComplex (Exists.choose (__fn_arg_req))))
  have __obj322_result : Litex.In (Litex.div 1 (Litex.arg __fn_arg 0)) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_152) (__wd0_154) (__wd0_151)))
  change Litex.In (Litex.div 1 (Litex.arg __fn_arg 0)) Litex.R
  exact (Litex.Rules.realDivClosure (__wd0_152) (__wd0_154) (__wd0_151) (Litex.Rules.numeralInR 1) (Exists.choose (__fn_arg_req)))

noncomputable def __reciprocal_impl : Litex.Object :=
  Litex.functionObject __reciprocal_spec __reciprocal_body

noncomputable def reciprocal : Litex.Object := __reciprocal_impl

theorem __fact259 : Litex.In reciprocal (Litex.FnSet ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, ∃ __h_dom0 : (Litex.arg __fn_arg 0) ≠ 0, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)) := by
  simpa only [reciprocal, __reciprocal_impl, __reciprocal_spec] using
    (Litex.functionObjectInFnSet __reciprocal_spec __reciprocal_body __reciprocal_closed)

theorem __fact260 : reciprocal = __reciprocal_impl := by
  rfl

theorem __fact270 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (__h0_2 : a ≠ 0), (reciprocal [a]) = (Litex.div 1 a) :=
by
  intro a __h0_1 __h0_2
  have __wd0_160 : Litex.In a Litex.R := by
    exact (__h0_1)
  have __wd0_161 : a ≠ 0 := by
    exact (__h0_2)
  have __obj333_app : Litex.Applicable (reciprocal) [a] := by
    exact (Litex.fnSetApplicable (args := [a]) __fact259 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, ∃ __h_dom0 : (a) ≠ 0, True
      exact Exists.intro (__wd0_160) (Exists.intro (__wd0_161) (True.intro))))
  have __obj333_result : Litex.In (reciprocal [a]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult (args := [a]) __fact259 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, ∃ __h_dom0 : (a) ≠ 0, True
      exact Exists.intro (__wd0_160) (Exists.intro (__wd0_161) (True.intro)))))
  have __wd0_162 : a ≠ 0 := by
    exact (__h0_2)
  have __wd0_163 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __wd0_164 : Litex.In a Litex.C := by
    exact ((Litex.Rules.realInComplex (__h0_1)))
  have __obj334_result : Litex.In (Litex.div 1 a) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_163) (__wd0_164) (__wd0_162)))
  exact (by
  change ((reciprocal) [a]) = (Litex.div 1 a)
  rw [__fact260]
  unfold __reciprocal_impl
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [__fact260, __reciprocal_impl] using __obj333_app)]
  simp only [__reciprocal_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

end __Sketch13

namespace __Sketch14

theorem __q_dim_pos : Litex.In 2 Litex.NPos := by
  exact (Litex.Rules.numeralInNPos 2 (by norm_num))

theorem __q_dim_ge2 : Litex.Le 2 2 := by
  exact (by
  exact (Litex.Rules.numeralLe 2 2).2 (by norm_num))

noncomputable def __q_value (__index89 : Litex.Object) : Litex.Object :=
  0

noncomputable def q : Litex.Object :=
  Litex.tupleObject 2 __q_value __q_dim_pos __q_dim_ge2

theorem __fact276 : Litex.IsTuple q :=
by
  unfold q
  exact Litex.tupleObjectIsTuple 2 __q_value __q_dim_pos __q_dim_ge2

theorem __fact277 : (Litex.tupleDim q) = 2 :=
by
  simpa only [q] using
    (Litex.tupleObject_dim 2 __q_value __q_dim_pos __q_dim_ge2)

theorem __fact284 : ∀ (_binder_90 : Litex.Object) (__h0_1 : Litex.In _binder_90 (Litex.closedRange 1 2)), (Litex.atIndex q _binder_90) = 0 :=
by
  intro __coord __coord_in_range
  simpa only [q, __q_value] using
    (Litex.tupleObject_at 2 __q_value __q_dim_pos __q_dim_ge2 __coord)

theorem __fact285 : q = q := by
  exact rfl

end __Sketch14

namespace __Sketch15

noncomputable def __litex_id_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)

noncomputable def __litex_id_body
    (__fn_arg : List Litex.Object)
    (__fn_arg_len : __fn_arg.length = __litex_id_spec.arity)
    (__fn_arg_req : __litex_id_spec.requirements __fn_arg) : Litex.Object :=
  (Litex.arg __fn_arg 0)

theorem __litex_id_closed :
    ∀ __fn_arg __fn_arg_len __fn_arg_req,
      Litex.In
        (__litex_id_body __fn_arg __fn_arg_len __fn_arg_req)
        (__litex_id_spec.range __fn_arg __fn_arg_len __fn_arg_req) := by
  intro __fn_arg __fn_arg_len __fn_arg_req
  change Litex.In (Litex.arg __fn_arg 0) Litex.R
  exact Exists.choose (__fn_arg_req)

noncomputable def __litex_id_impl : Litex.Object :=
  Litex.functionObject __litex_id_spec __litex_id_body

noncomputable def litex_id : Litex.Object := __litex_id_impl

theorem __fact290 : Litex.In litex_id (Litex.FnSet ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)) := by
  simpa only [litex_id, __litex_id_impl, __litex_id_spec] using
    (Litex.functionObjectInFnSet __litex_id_spec __litex_id_body __litex_id_closed)

theorem __fact291 : litex_id = __litex_id_impl := by
  rfl

theorem __fact299 : ∃ (x : Litex.Object), Litex.In x Litex.R ∧ x = 1 := by
  exact (by
  have __exist_step1 : (1 : Litex.Object) = 1 := by
    exact rfl
  exact ⟨1, (Litex.Rules.numeralInR 1), (__exist_step1)⟩)

noncomputable def y : Litex.Object := Classical.choose (__fact299)

theorem __fact304 : Litex.In y Litex.R := by
  unfold y
  exact (Classical.choose_spec (__fact299)).1

theorem __fact305 : y = 1 := by
  unfold y
  exact (Classical.choose_spec (__fact299)).2

theorem __fact306 : (litex_id [y]) = y := by
  have __wd0_182 : Litex.In y Litex.R := by
    exact (__fact304)
  have __obj387_app : Litex.Applicable (litex_id) [y] := by
    exact (Litex.fnSetApplicable (args := [y]) __fact290 rfl (by
      change ∃ __h_arg0 : Litex.In (y) Litex.R, True
      exact Exists.intro (__wd0_182) (True.intro)))
  have __obj387_result : Litex.In (litex_id [y]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult (args := [y]) __fact290 rfl (by
      change ∃ __h_arg0 : Litex.In (y) Litex.R, True
      exact Exists.intro (__wd0_182) (True.intro))))
  exact (by
  change ((litex_id) [y]) = y
  rw [__fact291]
  unfold __litex_id_impl
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [__fact291, __litex_id_impl] using __obj387_app)]
  simp only [__litex_id_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

theorem one_eq_one_by_cases : (1 : Litex.Object) = 1 :=
by
  have __step1 : (1 : Litex.Object) = 1 := by
    exact (by
  have __case1 : (1 : Litex.Object) = 1 := rfl
  exact __case1)
  exact rfl

noncomputable def __into_builder_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => (Litex.setBuilder Litex.R (fun __x99 => __x99 = __x99)) } : Litex.FnSpec)

noncomputable def __into_builder_body
    (__fn_arg : List Litex.Object)
    (__fn_arg_len : __fn_arg.length = __into_builder_spec.arity)
    (__fn_arg_req : __into_builder_spec.requirements __fn_arg) : Litex.Object :=
  (Litex.arg __fn_arg 0)

theorem __into_builder_closed :
    ∀ __fn_arg __fn_arg_len __fn_arg_req,
      Litex.In
        (__into_builder_body __fn_arg __fn_arg_len __fn_arg_req)
        (__into_builder_spec.range __fn_arg __fn_arg_len __fn_arg_req) := by
  intro __fn_arg __fn_arg_len __fn_arg_req
  change Litex.In (Litex.arg __fn_arg 0) (Litex.setBuilder Litex.R (fun __x99 => __x99 = __x99))
  exact (Litex.inSetBuilder_iff.mpr (And.intro (Exists.choose (__fn_arg_req)) ((rfl))))

noncomputable def __into_builder_impl : Litex.Object :=
  Litex.functionObject __into_builder_spec __into_builder_body

noncomputable def into_builder : Litex.Object := __into_builder_impl

theorem __fact325 : Litex.In into_builder (Litex.FnSet ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => (Litex.setBuilder Litex.R (fun __x99 => __x99 = __x99)) } : Litex.FnSpec)) := by
  simpa only [into_builder, __into_builder_impl, __into_builder_spec] using
    (Litex.functionObjectInFnSet __into_builder_spec __into_builder_body __into_builder_closed)

theorem __fact326 : into_builder = __into_builder_impl := by
  rfl

theorem __fact327 : (into_builder [1]) = 1 := by
  have __wd0_186 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have __obj406_app : Litex.Applicable (into_builder) [1] := by
    exact (Litex.fnSetApplicable (args := [1]) __fact325 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_186) (True.intro)))
  have __obj406_result : Litex.In (into_builder [1]) (Litex.setBuilder Litex.R (fun __x99 => __x99 = __x99)) := by
    exact (by simpa using (Litex.fnSetResult (args := [1]) __fact325 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_186) (True.intro))))
  exact (by
  change ((into_builder) [1]) = 1
  rw [__fact326]
  unfold __into_builder_impl
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [__fact326, __into_builder_impl] using __obj406_app)]
  simp only [__into_builder_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

end __Sketch15

namespace __Sketch16

theorem __wd0_189 : ∀ (__wd_scope8_arg1 : Litex.Object) (__wd_scope8_premise1 : Litex.In __wd_scope8_arg1 Litex.R), Litex.In __wd_scope8_arg1 Litex.R :=
by
  intro __wd_scope8_arg1 __wd_scope8_premise1
  exact __wd_scope8_premise1

theorem __wd0_190 : ∀ (__wd_scope9_arg1 : Litex.Object) (__wd_scope9_premise1 : Litex.In __wd_scope9_arg1 Litex.R), Litex.In __wd_scope9_arg1 Litex.R :=
by
  intro __wd_scope9_arg1 __wd_scope9_premise1
  exact __wd_scope9_premise1

noncomputable def __obj413 : Litex.Object :=
  Litex.R

noncomputable def __obj414 (__wd_scope8_arg1 : Litex.Object) : Litex.Object :=
  __wd_scope8_arg1

noncomputable def __obj415_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg0 => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg0 0) Litex.R, True, range := fun __fn_arg0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def __obj415_body (__obj415_arg : List Litex.Object) (__arg_len : __obj415_arg.length = (__obj415_spec).arity) (__arg_req : (__obj415_spec).requirements __obj415_arg) : Litex.Object :=
  (__obj414 ((Litex.arg __obj415_arg 0)))

theorem __obj415_closed :
    ∀ (__obj415_arg : List Litex.Object)
      (__obj415_arg_len : __obj415_arg.length = (__obj415_spec).arity)
      (__obj415_arg_req : (__obj415_spec).requirements __obj415_arg),
      Litex.In (__obj415_body __obj415_arg __obj415_arg_len __obj415_arg_req) ((__obj415_spec).range __obj415_arg __obj415_arg_len __obj415_arg_req) :=
by
  intro __obj415_arg __obj415_arg_len __obj415_arg_req
  change Litex.In (Litex.arg __obj415_arg 0) Litex.R
  exact (__wd0_189 ((Litex.arg __obj415_arg 0)) (Exists.choose (__obj415_arg_req)))

noncomputable def __obj415 : Litex.Object :=
  Litex.functionObject __obj415_spec __obj415_body

theorem __obj415_in_fn_space :
    Litex.In __obj415 (Litex.FnSet __obj415_spec) := by
  unfold __obj415
  exact Litex.functionObjectInFnSet __obj415_spec __obj415_body __obj415_closed

noncomputable def __obj416 : Litex.Object :=
  Litex.R

noncomputable def __obj417 (__wd_scope9_arg1 : Litex.Object) : Litex.Object :=
  __wd_scope9_arg1

noncomputable def __obj418_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg0 => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg0 0) Litex.R, True, range := fun __fn_arg0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def __obj418_body (__obj418_arg : List Litex.Object) (__arg_len : __obj418_arg.length = (__obj418_spec).arity) (__arg_req : (__obj418_spec).requirements __obj418_arg) : Litex.Object :=
  (__obj417 ((Litex.arg __obj418_arg 0)))

theorem __obj418_closed :
    ∀ (__obj418_arg : List Litex.Object)
      (__obj418_arg_len : __obj418_arg.length = (__obj418_spec).arity)
      (__obj418_arg_req : (__obj418_spec).requirements __obj418_arg),
      Litex.In (__obj418_body __obj418_arg __obj418_arg_len __obj418_arg_req) ((__obj418_spec).range __obj418_arg __obj418_arg_len __obj418_arg_req) :=
by
  intro __obj418_arg __obj418_arg_len __obj418_arg_req
  change Litex.In (Litex.arg __obj418_arg 0) Litex.R
  exact (__wd0_190 ((Litex.arg __obj418_arg 0)) (Exists.choose (__obj418_arg_req)))

noncomputable def __obj418 : Litex.Object :=
  Litex.functionObject __obj418_spec __obj418_body

theorem __obj418_in_fn_space :
    Litex.In __obj418 (Litex.FnSet __obj418_spec) := by
  unfold __obj418
  exact Litex.functionObjectInFnSet __obj418_spec __obj418_body __obj418_closed

theorem __fact334 : __obj415 = __obj418 := by
  exact rfl

theorem __wd0_197 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (__wd_scope14_arg1 : Litex.Object) (__wd_scope14_premise1 : Litex.In __wd_scope14_arg1 Litex.R), Litex.In __wd_scope14_arg1 Litex.R :=
by
  intro a __h0_1 __wd_scope14_arg1 __wd_scope14_premise1
  exact __wd_scope14_premise1

theorem __wd0_198 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.In a Litex.R :=
by
  intro a __h0_1
  exact __h0_1

noncomputable def __obj433 : Litex.Object :=
  Litex.R

noncomputable def __obj434 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def __obj435 (__wd_scope14_arg1 : Litex.Object) : Litex.Object :=
  __wd_scope14_arg1

noncomputable def __obj436_spec (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg0 => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg0 0) Litex.R, True, range := fun __fn_arg0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def __obj436_body (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (__obj436_arg : List Litex.Object) (__arg_len : __obj436_arg.length = ((__obj436_spec a __h0_1)).arity) (__arg_req : ((__obj436_spec a __h0_1)).requirements __obj436_arg) : Litex.Object :=
  (__obj435 ((Litex.arg __obj436_arg 0)))

theorem __obj436_closed (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) :
    ∀ (__obj436_arg : List Litex.Object)
      (__obj436_arg_len : __obj436_arg.length = ((__obj436_spec a __h0_1)).arity)
      (__obj436_arg_req : ((__obj436_spec a __h0_1)).requirements __obj436_arg),
      Litex.In ((__obj436_body a __h0_1) __obj436_arg __obj436_arg_len __obj436_arg_req) (((__obj436_spec a __h0_1)).range __obj436_arg __obj436_arg_len __obj436_arg_req) :=
by
  intro __obj436_arg __obj436_arg_len __obj436_arg_req
  change Litex.In (Litex.arg __obj436_arg 0) Litex.R
  exact (__wd0_197 (a) (__h0_1) ((Litex.arg __obj436_arg 0)) (Exists.choose (__obj436_arg_req)))

noncomputable def __obj436 (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.Object :=
  Litex.functionObject (__obj436_spec a __h0_1) (__obj436_body a __h0_1)

theorem __obj436_in_fn_space (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) :
    Litex.In (__obj436 a __h0_1) (Litex.FnSet (__obj436_spec a __h0_1)) := by
  unfold __obj436
  exact Litex.functionObjectInFnSet (__obj436_spec a __h0_1) (__obj436_body a __h0_1) (__obj436_closed a __h0_1)

theorem __obj437_app : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.Applicable (__obj436 a __h0_1) [(__obj434 a)] :=
by
  intro a __h0_1
  exact Litex.fnSetApplicable (args := [(__obj434 a)]) (__obj436_in_fn_space a __h0_1) rfl (by
  change ∃ __h_arg0 : Litex.In ((__obj434 a)) Litex.R, True
  exact Exists.intro ((__wd0_198 a __h0_1)) (True.intro))

noncomputable def __obj437 (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.Object :=
  (__obj436 a __h0_1) [(__obj434 a)]

theorem __obj437_result : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.In (__obj437 a __h0_1) Litex.R :=
by
  intro a __h0_1
  simpa [__obj437] using (Litex.fnSetResult (args := [(__obj434 a)]) (__obj436_in_fn_space a __h0_1) rfl (by
  change ∃ __h_arg0 : Litex.In ((__obj434 a)) Litex.R, True
  exact Exists.intro ((__wd0_198 a __h0_1)) (True.intro)))

theorem __wd0_199 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (__wd_scope15_arg1 : Litex.Object) (__wd_scope15_premise1 : Litex.In __wd_scope15_arg1 Litex.R), Litex.In __wd_scope15_arg1 Litex.R :=
by
  intro a __h0_1 __wd_scope15_arg1 __wd_scope15_premise1
  exact __wd_scope15_premise1

theorem __wd0_200 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.In a Litex.R :=
by
  intro a __h0_1
  exact __h0_1

noncomputable def __obj438 (__wd_scope15_arg1 : Litex.Object) : Litex.Object :=
  __wd_scope15_arg1

noncomputable def __obj439_spec (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg0 => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg0 0) Litex.R, True, range := fun __fn_arg0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def __obj439_body (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (__obj439_arg : List Litex.Object) (__arg_len : __obj439_arg.length = ((__obj439_spec a __h0_1)).arity) (__arg_req : ((__obj439_spec a __h0_1)).requirements __obj439_arg) : Litex.Object :=
  (__obj438 ((Litex.arg __obj439_arg 0)))

theorem __obj439_closed (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) :
    ∀ (__obj439_arg : List Litex.Object)
      (__obj439_arg_len : __obj439_arg.length = ((__obj439_spec a __h0_1)).arity)
      (__obj439_arg_req : ((__obj439_spec a __h0_1)).requirements __obj439_arg),
      Litex.In ((__obj439_body a __h0_1) __obj439_arg __obj439_arg_len __obj439_arg_req) (((__obj439_spec a __h0_1)).range __obj439_arg __obj439_arg_len __obj439_arg_req) :=
by
  intro __obj439_arg __obj439_arg_len __obj439_arg_req
  change Litex.In (Litex.arg __obj439_arg 0) Litex.R
  exact (__wd0_199 (a) (__h0_1) ((Litex.arg __obj439_arg 0)) (Exists.choose (__obj439_arg_req)))

noncomputable def __obj439 (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.Object :=
  Litex.functionObject (__obj439_spec a __h0_1) (__obj439_body a __h0_1)

theorem __obj439_in_fn_space (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) :
    Litex.In (__obj439 a __h0_1) (Litex.FnSet (__obj439_spec a __h0_1)) := by
  unfold __obj439
  exact Litex.functionObjectInFnSet (__obj439_spec a __h0_1) (__obj439_body a __h0_1) (__obj439_closed a __h0_1)

theorem __obj440_app : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.Applicable (__obj439 a __h0_1) [(__obj434 a)] :=
by
  intro a __h0_1
  exact Litex.fnSetApplicable (args := [(__obj434 a)]) (__obj439_in_fn_space a __h0_1) rfl (by
  change ∃ __h_arg0 : Litex.In ((__obj434 a)) Litex.R, True
  exact Exists.intro ((__wd0_200 a __h0_1)) (True.intro))

noncomputable def __obj440 (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.Object :=
  (__obj439 a __h0_1) [(__obj434 a)]

theorem __obj440_result : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.In (__obj440 a __h0_1) Litex.R :=
by
  intro a __h0_1
  simpa [__obj440] using (Litex.fnSetResult (args := [(__obj434 a)]) (__obj439_in_fn_space a __h0_1) rfl (by
  change ∃ __h_arg0 : Litex.In ((__obj434 a)) Litex.R, True
  exact Exists.intro ((__wd0_200 a __h0_1)) (True.intro)))

theorem __fact347 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), (__obj437 a __h0_1) = (__obj440 a __h0_1) :=
by
  intro a __h0_1
  exact rfl

end __Sketch16

namespace __Sketch17

theorem __fact369 : ∀ (f : Litex.Object) (__h0_1 : Litex.In f (Litex.fnSpace1 Litex.R Litex.R)) (__h0_2 : ∀ (y : Litex.Object) (__h1_1 : Litex.In y Litex.R), (f [y]) = (f [(Litex.sub y 1)])), (f [2]) = (f [1]) :=
by
  intro f __h0_1 __h0_2
  have __scope0 : ∀ (y : Litex.Object) (__h1_1 : Litex.In y Litex.R), Litex.In y Litex.R ∧ (Litex.Applicable (f) [y] ∧ (Litex.In (f [y]) Litex.R)) := by
    exact (by
      intro y __h1_1
      have __wd1_212 : Litex.In y Litex.R := by
        exact (__h1_1)
      have __obj477_app : Litex.Applicable (f) [y] := by
        exact (Litex.fnSpaceApplicable (args := [y]) __h0_1 rfl (by
          change ∃ __h_arg0 : Litex.In (y) Litex.R, True
          exact Exists.intro (__wd1_212) (True.intro)))
      have __obj477_result : Litex.In (f [y]) Litex.R := by
        exact (by simpa using (Litex.fnSpaceResult (args := [y]) __h0_1 rfl (by
          change ∃ __h_arg0 : Litex.In (y) Litex.R, True
          exact Exists.intro (__wd1_212) (True.intro))))
      exact And.intro (__wd1_212) (And.intro (__obj477_app) ((__obj477_result))))
  have __scope1 : ∀ (y : Litex.Object) (__h1_1 : Litex.In y Litex.R), Litex.In y Litex.C ∧ (Litex.In 1 Litex.C ∧ (Litex.In 1 Litex.R ∧ (Litex.In (Litex.sub y 1) Litex.R ∧ (Litex.In (Litex.sub y 1) Litex.C ∧ (Litex.Applicable (f) [(Litex.sub y 1)] ∧ (Litex.In (f [(Litex.sub y 1)]) Litex.R)))))) := by
    exact (by
      intro y __h1_1
      have __wd1_213 : Litex.In y Litex.C := by
        exact ((Litex.Rules.realInComplex (__h1_1)))
      have __wd1_214 : Litex.In 1 Litex.C := by
        exact (Litex.Rules.numeralInC 1)
      have __wd1_215 : Litex.In 1 Litex.R := by
        exact (Litex.Rules.numeralInR 1)
      have __wd1_216 : Litex.In (Litex.sub y 1) Litex.R := by
        exact ((Litex.Rules.realSubClosure (__wd1_213) (__wd1_214) (__h1_1) (Litex.Rules.numeralInR 1)))
      have __obj480_result : Litex.In (Litex.sub y 1) Litex.C := by
        exact ((Litex.Rules.complexSubClosure (__wd1_213) (__wd1_214)))
      have __obj481_app : Litex.Applicable (f) [(Litex.sub y 1)] := by
        exact (Litex.fnSpaceApplicable (args := [(Litex.sub y 1)]) __h0_1 rfl (by
          change ∃ __h_arg0 : Litex.In ((Litex.sub y 1)) Litex.R, True
          exact Exists.intro (__wd1_216) (True.intro)))
      have __obj481_result : Litex.In (f [(Litex.sub y 1)]) Litex.R := by
        exact (by simpa using (Litex.fnSpaceResult (args := [(Litex.sub y 1)]) __h0_1 rfl (by
          change ∃ __h_arg0 : Litex.In ((Litex.sub y 1)) Litex.R, True
          exact Exists.intro (__wd1_216) (True.intro))))
      exact And.intro (__wd1_213) (And.intro (__wd1_214) (And.intro (__wd1_215) (And.intro (__wd1_216) (And.intro (__obj480_result) (And.intro (__obj481_app) ((__obj481_result))))))))
  have __wd0_217 : Litex.In 2 Litex.R := by
    exact (Litex.Rules.numeralInR 2)
  have __obj484_app : Litex.Applicable (f) [2] := by
    exact (Litex.fnSpaceApplicable (args := [2]) __h0_1 rfl (by
      change ∃ __h_arg0 : Litex.In (2) Litex.R, True
      exact Exists.intro (__wd0_217) (True.intro)))
  have __obj484_result : Litex.In (f [2]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [2]) __h0_1 rfl (by
      change ∃ __h_arg0 : Litex.In (2) Litex.R, True
      exact Exists.intro (__wd0_217) (True.intro))))
  have __wd0_218 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have __obj486_app : Litex.Applicable (f) [1] := by
    exact (Litex.fnSpaceApplicable (args := [1]) __h0_1 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_218) (True.intro)))
  have __obj486_result : Litex.In (f [1]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [1]) __h0_1 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_218) (True.intro))))
  exact (by
  have __normalized := ((__h0_2 (Litex.add 1 1) ((Litex.Rules.realAddClosure ((Litex.Rules.numeralInC 1)) ((Litex.Rules.numeralInC 1)) (Litex.Rules.numeralInR 1) (Litex.Rules.numeralInR 1)))))
  simp only [OfNat.ofNat, Litex.add_embedComplex, Litex.sub_embedComplex, Litex.mul_embedComplex, Litex.div_embedComplex] at __normalized ⊢
  norm_num at __normalized ⊢
  exact __normalized)

end __Sketch17

namespace __Sketch18

axiom marked : Litex.Object → Prop

def is_zero (x : Litex.Object) : Prop :=
  Litex.In x Litex.R ∧ (x = 0)

theorem __fact372 : is_zero 0 := by
  exact (by
  change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0)
  exact And.intro (Litex.Rules.numeralInR 0) ((rfl)))

theorem __fact373 : Litex.In 0 Litex.R := by
  exact (by
  have __definition := (__fact372)
  change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0) at __definition
  exact (__definition).1)

theorem __fact374 : (0 : Litex.Object) = 0 := by
  exact (by
  have __definition := (__fact372)
  change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0) at __definition
  exact (__definition).2)

noncomputable def named_zero : Litex.Object := 0

theorem __fact376 : Litex.In named_zero Litex.R := by
  simpa only [named_zero] using (__fact373)

theorem __fact377 : named_zero = 0 := by
  rfl

theorem __fact378 : is_zero named_zero := by
  exact (by
  change Litex.In named_zero Litex.R ∧ (named_zero = 0)
  exact And.intro (__fact376) ((__fact377)))

axiom __fact379 : marked named_zero

end __Sketch18

namespace __Sketch19

theorem __fact392 : ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a) (b : Litex.Object) (__h0_2 : Litex.IsSet b) (__h0_3 : a = b), b = a :=
by
  intro a __h0_1 b __h0_2 __h0_3
  exact (Eq.symm (__h0_3))

theorem __fact411 : ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a) (b : Litex.Object) (__h0_2 : Litex.IsSet b) (c : Litex.Object) (__h0_3 : Litex.IsSet c) (__h0_4 : a = b) (__h0_5 : b = c), a = c :=
by
  intro a __h0_1 b __h0_2 c __h0_3 __h0_4 __h0_5
  exact (Eq.trans ((__h0_4)) ((__h0_5)))

end __Sketch19

namespace __Sketch20

theorem __fact438 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (__h0_2 : a = 1), Litex.In 1 Litex.R :=
by
  intro a __h0_1 __h0_2
  exact Litex.Rules.numeralInR 1

theorem __fact439 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (__h0_2 : a = 1), Litex.In a Litex.R :=
by
  intro a __h0_1 __h0_2
  exact by simpa only [__h0_2] using (__fact438 a __h0_1 __h0_2)

theorem __fact437 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (f : Litex.Object) (__h0_2 : Litex.In f (Litex.fnSpace1 Litex.R Litex.R)) (__h0_3 : a = 1), (f [a]) = (f [a]) :=
by
  intro a __h0_1 f __h0_2 __h0_3
  have __wd0_228 : Litex.In a Litex.R := by
    exact (by simpa only [__h0_3] using (__fact438 a __h0_1 __h0_3))
  have __wd0_229 : Litex.In a Litex.R := by
    exact (__fact439 a __h0_1 __h0_3)
  have __obj552_app : Litex.Applicable (f) [a] := by
    exact (Litex.fnSpaceApplicable (args := [a]) __h0_2 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, True
      exact Exists.intro (__wd0_229) (True.intro)))
  have __obj552_result : Litex.In (f [a]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [a]) __h0_2 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, True
      exact Exists.intro (__wd0_229) (True.intro))))
  exact rfl

end __Sketch20

namespace __Sketch21

theorem __fact452 : ∀ (s : Litex.Object) (__h0_1 : Litex.IsNonemptySet s), s = s :=
by
  intro s __h0_1
  exact rfl

theorem __fact453 : ∀ (t : Litex.Object) (__h0_1 : Litex.IsFiniteSet t), t = t :=
by
  intro t __h0_1
  exact rfl

end __Sketch21

namespace __Sketch22

theorem __fact466 : ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a) (b : Litex.Object) (__h0_2 : Litex.IsSet b) (__h0_3 : a ≠ b), b ≠ a :=
by
  intro a __h0_1 b __h0_2 __h0_3
  exact (Litex.Rules.notEqualSymmetry (__h0_3))

theorem __fact467 : Litex.In 1 Litex.N := by
  exact Litex.Rules.numeralInN 1

theorem __fact468 : Litex.Le 0 1 := by
  exact (by
  exact (Litex.Rules.numeralLe 0 1).2 (by norm_num))

theorem __fact470 : Litex.In 1 Litex.C := by
  exact Litex.Rules.numeralInC 1

end __Sketch22

namespace __Sketch23

noncomputable def one : Litex.Object := 1

theorem __fact472 : Litex.In one Litex.Z := by
  simpa only [one] using (Litex.Rules.numeralInZ 1)

theorem __fact473 : one = 1 := by
  rfl

noncomputable def integer_set : Litex.Object := Litex.Z

theorem __fact475 : Litex.IsSet integer_set := by
  simpa only [integer_set] using (Litex.Rules.objectIsSet Litex.Z)

theorem __fact476 : integer_set = Litex.Z := by
  rfl

theorem __fact477 : Litex.In (Litex.add one 1) integer_set := by
  have __wd0_231 : Litex.In one Litex.C := by
    exact (by simpa only [__fact473] using (Litex.Rules.numeralInC 1))
  have __wd0_232 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __obj589_result : Litex.In (Litex.add one 1) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_231) (__wd0_232)))
  exact by simpa only [__fact476, __fact473] using ((by
  have __normalized := (Litex.Rules.numeralInZ 2)
  simp only [OfNat.ofNat, Litex.add_embedComplex, Litex.sub_embedComplex, Litex.mul_embedComplex, Litex.div_embedComplex] at __normalized ⊢
  norm_num at __normalized ⊢
  exact __normalized))

theorem __fact478 : Litex.In (Litex.add one 1) Litex.Z := by
  have __wd0_231 : Litex.In one Litex.C := by
    exact (by simpa only [__fact473] using (Litex.Rules.numeralInC 1))
  have __wd0_232 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __obj589_result : Litex.In (Litex.add one 1) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_231) (__wd0_232)))
  exact by simpa only [__fact476] using (__fact477)

end __Sketch23

namespace __Sketch24

example : (1 : Litex.Object) = 1 :=
by
  have __step_1 : (2 : Litex.Object) = 2 := by
    exact (rfl)
  exact rfl

example : ∀ (x : Litex.Object) (__h0_1 : Litex.In x Litex.R), x = x :=
by
  intro x __h0_1
  exact rfl

namespace __Sketch01

theorem __fact483 : (3 : Litex.Object) = 3 := by
  exact rfl

end __Sketch01

end __Sketch24

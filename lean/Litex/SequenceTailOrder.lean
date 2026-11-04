import Litex.BuiltinSequence

universe u
open Filter
open scoped Topology
namespace Litex

private theorem eventually_sequence_tail {M : Semantics.{u}} [F : FunctionSemantics M]
    (cutoff : M.Value) (hc : M.mem cutoff (denote (NPos (M := M)))) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      M.mem (M.number (n : ℂ)) (denote (NPos (M := M))) ∧
      RealLeValue M cutoff (M.number (n : ℂ)) := by
  let c := semanticObject cutoff (M.member_isSet hc)
  obtain ⟨k, hk⟩ := (M.natural_members cutoff).mp (inNPos_natural c hc)
  filter_upwards [eventually_ge_atTop (Max.max (1 : ℕ) k)] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left _ _) hn)
  refine ⟨hnpos, numberInNPosOfEq (n : ℂ) n rfl hnpos, ?_⟩
  rw [hk]
  apply (realLeValue_numbers (M := M) (k : ℝ) (n : ℝ)).mpr
  exact_mod_cast le_trans (le_max_right 1 k) hn

theorem sequenceLimitEventuallyEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b value cutoff : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : M.mem value (denote (R (M := M))))
    (hc : M.mem cutoff (denote (NPos (M := M))))
    (hl : HasSequenceLimitValue M a value)
    (he : ∀ n, M.mem n (denote (NPos (M := M))) →
      RealLeValue M cutoff n → F.callValue a n = F.callValue b n) :
    HasSequenceLimitValue M b value := by
  obtain ⟨r, hr⟩ := (M.real_members value).mp hv
  rw [hr] at hl ⊢
  apply (sequenceLimit_iff_tendsto b r hb).mpr
  apply ((sequenceLimit_iff_tendsto a r ha).mp hl).congr'
  filter_upwards [eventually_sequence_tail cutoff hc] with n hn
  exact congrArg observeRealValue (he _ hn.2.1 hn.2.2)

theorem sequenceLimitShift {M : Semantics.{u}} [F : FunctionSemantics M]
    (a value amount : M.Value) (g : Obj (M := M) (FormulaFn M))
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : M.mem value (denote (R (M := M))))
    (hm : M.mem amount (denote (N (M := M))))
    (hl : HasSequenceLimitValue M a value)
    (hD : g.val.signature.domain = denote (NPos (M := M)))
    (hR : g.val.signature.output = denote (R (M := M)))
    (hbody : g.val.bodyValue = fun n => F.callValue a (M.addValue n amount)) :
    HasSequenceLimitValue M (denote g) value := by
  have hg : M.mem (denote g) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))) := by
    have h := formulaFnInFnSet g
    change M.mem (denote g) (F.fnSetValue g.val.signature.domain g.val.signature.output) at h
    rwa [hD, hR] at h
  obtain ⟨r, hr⟩ := (M.real_members value).mp hv
  obtain ⟨k, hk⟩ := (M.natural_members amount).mp hm
  rw [hr] at hl ⊢
  apply (sequenceLimit_iff_tendsto (denote g) r hg).mpr
  have ht := ((sequenceLimit_iff_tendsto a r ha).mp hl).comp (tendsto_add_atTop_nat k)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hd : M.mem (M.number (n : ℂ)) g.val.signature.domain :=
    hD.symm ▸ numberInNPosOfEq (n : ℂ) n rfl hnpos
  have hcall : F.callValue (denote g) (M.number (n : ℂ)) = g.val.bodyValue (M.number (n : ℂ)) :=
    F.call_graphValue _ _ _ g.wd _ hd
  change observeRealSequence a (n + k) = observeRealValue (F.callValue (denote g) (M.number (n : ℂ)))
  rw [hcall, hbody]
  dsimp only
  rw [hk, M.add_numbers, ← Nat.cast_add]
  rfl

theorem sequenceLimitCompare {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b left right cutoff : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hl : M.mem left (denote (R (M := M)))) (hr : M.mem right (denote (R (M := M))))
    (hc : M.mem cutoff (denote (NPos (M := M))))
    (hla : HasSequenceLimitValue M a left) (hlb : HasSequenceLimitValue M b right)
    (ho : ∀ n, M.mem n (denote (NPos (M := M))) →
      RealLeValue M cutoff n → RealLeValue M (F.callValue a n) (F.callValue b n)) :
    RealLeValue M left right := by
  obtain ⟨l, hleft⟩ := (M.real_members left).mp hl
  obtain ⟨r, hright⟩ := (M.real_members right).mp hr
  rw [hleft] at hla
  rw [hright] at hlb
  rw [hleft, hright]
  apply (realLeValue_numbers l r).mpr
  apply le_of_tendsto_of_tendsto ((sequenceLimit_iff_tendsto a l ha).mp hla)
    ((sequenceLimit_iff_tendsto b r hb).mp hlb)
  filter_upwards [eventually_sequence_tail cutoff hc] with n hn
  have h := ho _ hn.2.1 hn.2.2
  rw [observeRealSequence_spec a n hn.1 ha, observeRealSequence_spec b n hn.1 hb] at h
  exact (realLeValue_numbers _ _).mp h

theorem sequenceLimitSqueeze {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b c value cutoff : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hc : M.mem c (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : M.mem value (denote (R (M := M))))
    (hcut : M.mem cutoff (denote (NPos (M := M))))
    (hla : HasSequenceLimitValue M a value) (hlc : HasSequenceLimitValue M c value)
    (ho : ∀ n, M.mem n (denote (NPos (M := M))) → RealLeValue M cutoff n →
      RealLeValue M (F.callValue a n) (F.callValue b n) ∧
      RealLeValue M (F.callValue b n) (F.callValue c n)) :
    HasSequenceLimitValue M b value := by
  obtain ⟨r, hr⟩ := (M.real_members value).mp hv
  rw [hr] at hla hlc ⊢
  apply (sequenceLimit_iff_tendsto b r hb).mpr
  have hbounds : ∀ᶠ n : ℕ in atTop,
      observeRealSequence a n ≤ observeRealSequence b n ∧
      observeRealSequence b n ≤ observeRealSequence c n := by
    filter_upwards [eventually_sequence_tail cutoff hcut] with n hn
    have h := ho _ hn.2.1 hn.2.2
    rw [observeRealSequence_spec a n hn.1 ha, observeRealSequence_spec b n hn.1 hb,
      observeRealSequence_spec c n hn.1 hc] at h
    exact ⟨(realLeValue_numbers _ _).mp h.1, (realLeValue_numbers _ _).mp h.2⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((sequenceLimit_iff_tendsto a r ha).mp hla)
    ((sequenceLimit_iff_tendsto c r hc).mp hlc) (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2)

theorem sequenceLimitExistsOfConvergent {M : Semantics.{u}} [FunctionSemantics M]
    (a : M.Value) (h : SequenceConvergentValue M a) :
    ∃ value : Obj (M := M) M.Value, In value R ∧ HasSequenceLimitValue M a (denote value) := by
  obtain ⟨value, hv, hl⟩ := h
  exact ⟨value, hv, hl⟩

end Litex

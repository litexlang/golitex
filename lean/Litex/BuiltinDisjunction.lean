import Litex.ElementaryFunctions
universe u
namespace Litex

theorem realTrichotomyValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real)) :
    a=b ∨ realBound false a b ∨ realBound false b a := by
  obtain ⟨r,hr⟩ := (M.real_members a).mp ha
  obtain ⟨s,hs⟩ := (M.real_members b).mp hb
  rcases lt_trichotomy r s with h | h | h
  · exact Or.inr (Or.inl ⟨r,s,hr,hs,h⟩)
  · exact Or.inl (hr.trans ((congrArg (fun t : ℝ => M.number (t : ℂ)) h).trans hs.symm))
  · exact Or.inr (Or.inr ⟨s,r,hs,hr,h⟩)

theorem realWeakTotalValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real)) :
    realBound true a b ∨ realBound true b a := by
  obtain ⟨r,hr⟩ := (M.real_members a).mp ha
  obtain ⟨s,hs⟩ := (M.real_members b).mp hb
  rcases le_total r s with h | h
  · exact Or.inl ⟨r,s,hr,hs,h⟩
  · exact Or.inr ⟨s,r,hs,hr,h⟩

theorem naturalZeroOrAtLeastOneValue {M : Semantics.{u}} (a : M.Value)
    (ha : M.mem a (M.standard .natural)) :
    a = M.number 0 ∨ realBound true (M.number 1) a := by
  obtain ⟨n,hn⟩ := (M.natural_members a).mp ha
  by_cases h : n=0
  · subst n
    exact Or.inl (by simpa only [Nat.cast_zero] using hn)
  · apply Or.inr
    refine ⟨1,(n : ℝ),?_,?_,?_⟩
    · simp only [Complex.ofReal_one]
    · simpa only [Complex.ofReal_natCast] using hn
    · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
theorem absoluteSignSplitValue {M : Semantics.{u}} (subtract : Bool) (a : M.Value)
    (ha : M.mem a (M.standard .real)) :
    absValue a = a ∨ absValue a = (if subtract then M.subValue (M.number 0) a else M.negValue a) := by
  obtain ⟨r,hr⟩ := (M.real_members a).mp ha
  rcases le_total 0 r with h | h
  · exact Or.inl (by rw [hr,absValue_number,abs_of_nonneg h])
  · apply Or.inr
    cases subtract
    · simp only [Bool.false_eq_true,if_false]
      rw [hr,absValue_number,M.neg_numbers,abs_of_nonpos h,Complex.ofReal_neg]
    · simp only [if_true]
      rw [hr,absValue_number,M.sub_numbers,zero_sub,abs_of_nonpos h,Complex.ofReal_neg]
theorem integerDiscreteSuccessorValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .integer)) (hb : M.mem b (M.standard .integer)) :
    realBound true a b ∨ realBound true (M.addValue b (M.number 1)) a := by
  obtain ⟨k,hk⟩ := (M.integer_members a).mp ha
  obtain ⟨n,hn⟩ := (M.integer_members b).mp hb
  rcases le_or_gt k n with h | h
  · exact Or.inl ⟨(k : ℝ),(n : ℝ),by simpa only [Complex.ofReal_intCast] using hk,
      by simpa only [Complex.ofReal_intCast] using hn,by exact_mod_cast h⟩
  · apply Or.inr
    refine ⟨((n+1 : ℤ) : ℝ),(k : ℝ),?_,?_,?_⟩
    · rw [hn,M.add_numbers]
      push_cast
      rfl
    · simpa only [Complex.ofReal_intCast] using hk
    · exact_mod_cast (show n+1≤k by omega)

theorem integerDiscretePredecessorValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .integer)) (hb : M.mem b (M.standard .integer)) :
    realBound true b a ∨ realBound true a (M.subValue b (M.number 1)) := by
  obtain ⟨k,hk⟩ := (M.integer_members a).mp ha
  obtain ⟨n,hn⟩ := (M.integer_members b).mp hb
  rcases le_or_gt n k with h | h
  · exact Or.inl ⟨(n : ℝ),(k : ℝ),by simpa only [Complex.ofReal_intCast] using hn,
      by simpa only [Complex.ofReal_intCast] using hk,by exact_mod_cast h⟩
  · apply Or.inr
    refine ⟨(k : ℝ),((n-1 : ℤ) : ℝ),?_,?_,?_⟩
    · simpa only [Complex.ofReal_intCast] using hk
    · rw [hn,M.sub_numbers]
      push_cast
      rfl
    · exact_mod_cast (show k≤n-1 by omega)
universe v w
theorem remainderResidueWitness {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ModObj (M := M) α β)) (m : ℤ) (hpos : 0 < m)
    (hm : denote p.val.right = M.number (m : ℂ)) :
    ∃ k : ℤ, 0 ≤ k ∧ k < m ∧ denote p = M.number (k : ℂ) := by
  obtain ⟨a,ha⟩ := (M.integer_members _).mp p.wd.1
  exact ⟨a % m,Int.emod_nonneg a (ne_of_gt hpos),Int.emod_lt_of_pos a hpos,modDenoteInt p a m ha hm⟩
theorem classicalImplicationDisjunction (A B : Prop) (h : A → B) : ¬A ∨ B := by
  classical
  by_cases ha : A
  · exact Or.inr (h ha)
  · exact Or.inl ha
end Litex

import Litex.SetFunctions

universe u v w

namespace Litex

theorem positiveNaturalAboveReal {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a R) :
    ∃ n : Obj (M := M) M.Value, ∃ _ : In n NPos, Lt a n := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  obtain ⟨n, hn⟩ := exists_nat_gt (max r 0)
  have hpositive : 0 < n := by
    exact_mod_cast lt_of_le_of_lt (le_max_right r 0) hn
  have hmember := numberInNPosOfEq (M := M) (n : ℂ) n rfl hpositive
  let value := semanticObject (M.number (n : ℂ)) (M.member_isSet hmember)
  refine ⟨value, hmember, ?_⟩
  refine NativeBridge.ltOfDenoteReal a value r (n : ℝ) hr ?_
    (lt_of_le_of_lt (le_max_left r 0) hn)
  change M.number (n : ℂ) = M.number ((n : ℝ) : ℂ)
  rw [Complex.ofReal_natCast]

theorem rationalBetweenRealObjects {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a R) (hb : In b R) (hab : Lt a b) :
    ∃ q : Obj (M := M) M.Value, ∃ _ : In q Q, Lt a q ∧ Lt q b := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  obtain ⟨s, hs⟩ := (M.real_members _).mp hb
  have horder : r < s := (NativeBridge.lt_iff_ofDenoteReal a b r s hr hs).mp hab
  obtain ⟨q, hleft, hright⟩ := exists_rat_btwn horder
  have hmember : M.mem (M.number (q : ℂ)) (M.standard .rational) :=
    (M.rational_members _).mpr ⟨q, rfl⟩
  let value := semanticObject (M.number (q : ℂ)) (M.member_isSet hmember)
  have hvalue : denote value = M.number ((q : ℝ) : ℂ) := by
    change M.number (q : ℂ) = M.number ((q : ℝ) : ℂ)
    rw [Complex.ofReal_ratCast]
  exact ⟨value, hmember,
    NativeBridge.ltOfDenoteReal a value r (q : ℝ) hr hvalue hleft,
    NativeBridge.ltOfDenoteReal value b (q : ℝ) s hvalue hs hright⟩


theorem reciprocalNaturalWitness {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (epsilon : Obj (M := M) α)
    (hepsilon : In epsilon RPos) :
    ∃ n : Obj (M := M) M.Value, ∃ _ : In n NPos,
      ∃ r s : ℝ, M.divValue (M.number 1) (denote n) = M.number (r : ℂ) ∧
        denote epsilon = M.number (s : ℂ) ∧ r < s := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp (inRPos_real epsilon hepsilon)
  have hrpos : 0 < r :=
    (NativeBridge.lt_iff_ofDenoteReal _ _ 0 r rfl hr).mp (inRPos_positive epsilon hepsilon)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hrpos
  let m := n + 1
  have hm : 0 < m := Nat.succ_pos n
  have hbound : 1 / (m : ℝ) < r := by
    simpa only [m, Nat.cast_add, Nat.cast_one] using hn
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hmember := numberInNPosOfEq (M := M) (m : ℂ) m rfl hm
  let value := semanticObject (M.number (m : ℂ)) (M.member_isSet hmember)
  refine ⟨value, hmember, 1 / (m : ℝ), r, ?_, hr, hbound⟩
  change M.divValue (M.number (1 : ℂ)) (M.number (m : ℂ)) = M.number ((1 / (m : ℝ) : ℝ) : ℂ)
  rw [M.div_numbers _ _ hmC, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]

theorem realMidpointWitness {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a R) (hb : In b R) (hab : Lt a b) :
    ∃ x : Obj (M := M) M.Value, ∃ _ : In x R, Lt a x ∧ Lt x b := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  obtain ⟨s, hs⟩ := (M.real_members _).mp hb
  have hrs : r < s := (NativeBridge.lt_iff_ofDenoteReal a b r s hr hs).mp hab
  let midpoint := (r + s) / 2
  have hleft : r < midpoint := by dsimp [midpoint]; linarith
  have hright : midpoint < s := by dsimp [midpoint]; linarith
  have hmember := NativeBridge.numberInROfEq (M := M) (midpoint : ℂ) midpoint rfl
  let value := semanticObject (M.number (midpoint : ℂ)) (M.member_isSet hmember)
  exact ⟨value, hmember,
    NativeBridge.ltOfDenoteReal a value r midpoint hr rfl hleft,
    NativeBridge.ltOfDenoteReal value b midpoint s rfl hs hright⟩

end Litex

import Litex.Scalar

universe u v w x

namespace Litex.NumericModel

/-- An example-only encoding through a chosen well-order, not a selected
production representation of Litex numbers. -/
noncomputable def codeComplex (z : ℂ) : ZFSet.{0} :=
  Ordinal.toZFSet (Ordinal.typein (@WellOrderingRel ℂ) z)

theorem codeComplex_injective : Function.Injective codeComplex := by
  intro x y h
  exact Ordinal.typein_injective (@WellOrderingRel ℂ)
    (Ordinal.toZFSet_injective h)

/-- Decode an encoded complex value. The zero branch merely totalizes this
example model outside C; the public arithmetic constructors require C-membership
and never authorize that branch as the meaning of an arbitrary object. -/
noncomputable def decodeComplex (x : ZFSet.{0}) : ℂ := by
  classical
  exact if h : ∃ z : ℂ, codeComplex z = x then Classical.choose h else 0

@[simp] theorem decodeComplex_codeComplex (z : ℂ) :
    decodeComplex (codeComplex z) = z := by
  classical
  have h : ∃ w : ℂ, codeComplex w = codeComplex z := ⟨z, rfl⟩
  unfold decodeComplex
  rw [dif_pos h]
  exact codeComplex_injective (Classical.choose_spec h)

/-- All five standard sets are actual ZF sets of the corresponding embedded
native numbers. No standard-set tag stands for the whole semantic universe. -/
noncomputable def standardSet : StandardSetValue → ZFSet.{0}
  | .natural => ZFSet.range (fun n : ℕ => codeComplex (n : ℂ))
  | .integer => ZFSet.range (fun n : ℤ => codeComplex (n : ℂ))
  | .rational => ZFSet.range (fun q : ℚ => codeComplex (q : ℂ))
  | .real => ZFSet.range (fun r : ℝ => codeComplex (r : ℂ))
  | .complex => ZFSet.range codeComplex

theorem complex_members (x : ZFSet.{0}) :
    x ∈ standardSet .complex ↔ ∃ z : ℂ, x = codeComplex z := by
  simp only [standardSet, ZFSet.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

theorem natural_members (x : ZFSet.{0}) :
    x ∈ standardSet .natural ↔ ∃ n : ℕ, x = codeComplex (n : ℂ) := by
  simp only [standardSet, ZFSet.mem_range]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm⟩

theorem integer_members (x : ZFSet.{0}) :
    x ∈ standardSet .integer ↔ ∃ z : ℤ, x = codeComplex (z : ℂ) := by
  simp only [standardSet, ZFSet.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

theorem rational_members (x : ZFSet.{0}) :
    x ∈ standardSet .rational ↔ ∃ q : ℚ, x = codeComplex (q : ℂ) := by
  simp only [standardSet, ZFSet.mem_range]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.symm⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.symm⟩

theorem real_members (x : ZFSet.{0}) :
    x ∈ standardSet .real ↔ ∃ r : ℝ, x = codeComplex (r : ℂ) := by
  simp only [standardSet, ZFSet.mem_range]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, hr.symm⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, hr.symm⟩

theorem real_subset_complex (x : ZFSet.{0})
    (hx : x ∈ standardSet .real) : x ∈ standardSet .complex := by
  obtain ⟨r, rfl⟩ := (real_members x).mp hx
  exact (complex_members (codeComplex (r : ℂ))).mpr ⟨(r : ℂ), rfl⟩

noncomputable def addValue (a b : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a + decodeComplex b)

noncomputable def subValue (a b : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a - decodeComplex b)

noncomputable def mulValue (a b : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a * decodeComplex b)

noncomputable def negValue (a : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (-decodeComplex a)

noncomputable def divValue (a b : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a / decodeComplex b)

/-- Totalization outside the certified integer-power domain belongs only to
this explicit candidate model. The public constructor retains the exponent
object and evidence identifying it with an exact integer. -/
noncomputable def powValue (a e : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a ^ (⌊(decodeComplex e).re⌋ : ℤ))

theorem add_numbers (a b : ℂ) :
    addValue (codeComplex a) (codeComplex b) = codeComplex (a + b) := by
  simp only [addValue, decodeComplex_codeComplex]

theorem sub_numbers (a b : ℂ) :
    subValue (codeComplex a) (codeComplex b) = codeComplex (a - b) := by
  simp only [subValue, decodeComplex_codeComplex]

theorem mul_numbers (a b : ℂ) :
    mulValue (codeComplex a) (codeComplex b) = codeComplex (a * b) := by
  simp only [mulValue, decodeComplex_codeComplex]

theorem neg_numbers (a : ℂ) :
    negValue (codeComplex a) = codeComplex (-a) := by
  simp only [negValue, decodeComplex_codeComplex]

theorem div_numbers (a b : ℂ) (_hb : b ≠ 0) :
    divValue (codeComplex a) (codeComplex b) = codeComplex (a / b) := by
  simp only [divValue, decodeComplex_codeComplex]

theorem pow_numbers_nat (a : ℂ) (n : ℕ) :
    powValue (codeComplex a) (codeComplex (n : ℂ)) = codeComplex (a ^ n) := by
  simp only [powValue, decodeComplex_codeComplex, Complex.natCast_re, Int.floor_natCast,
    zpow_natCast]

theorem pow_numbers_int (a : ℂ) (z : ℤ) (_ha : a ≠ 0) :
    powValue (codeComplex a) (codeComplex (z : ℂ)) = codeComplex (a ^ z) := by
  simp only [powValue, decodeComplex_codeComplex, Complex.intCast_re, Int.floor_intCast]

theorem add_closed {a b : ZFSet.{0}}
    (ha : a ∈ standardSet .complex) (hb : b ∈ standardSet .complex) :
    addValue a b ∈ standardSet .complex := by
  obtain ⟨x, rfl⟩ := (complex_members a).mp ha
  obtain ⟨y, rfl⟩ := (complex_members b).mp hb
  exact (complex_members _).mpr ⟨x + y, add_numbers x y⟩

theorem div_closed {a b : ZFSet.{0}}
    (ha : a ∈ standardSet .complex) (hb : b ∈ standardSet .complex)
    (hb0 : b ≠ codeComplex 0) : divValue a b ∈ standardSet .complex := by
  obtain ⟨x, rfl⟩ := (complex_members a).mp ha
  obtain ⟨y, rfl⟩ := (complex_members b).mp hb
  have hy0 : y ≠ 0 := fun h => hb0 (congrArg codeComplex h)
  exact (complex_members _).mpr ⟨x / y, div_numbers x y hy0⟩

/-- A concrete candidate for the numeric object interface. The supported set
and function contracts have separate instances below; this is not a complete
interpretation of all Litex objects and rules. Every Value is
already a genuine ZF set, so its sethood predicate is True. Membership is
actual ZF membership and equality is faithful
to the injective encoding; neither proposition is trivialized. Arithmetic is
only source-valid under the separate WD/domain proofs required by Litex.Obj.
This witness installs no default model or Representation for arbitrary types. -/
noncomputable def model : Semantics.{1} where
  Value := ZFSet.{0}
  mem := fun x A => x ∈ A
  isSet := fun _ => True
  number := codeComplex
  standard := standardSet
  addValue := addValue
  subValue := subValue
  mulValue := mulValue
  negValue := negValue
  divValue := divValue
  powValue := powValue
  number_injective := codeComplex_injective
  complex_members := complex_members
  natural_members := natural_members
  integer_members := integer_members
  rational_members := rational_members
  real_members := real_members
  real_subset_complex := real_subset_complex
  member_isSet := fun _ => True.intro
  standard_isSet := fun _ => True.intro
  add_numbers := add_numbers
  sub_numbers := sub_numbers
  mul_numbers := mul_numbers
  neg_numbers := neg_numbers
  div_numbers := div_numbers
  pow_numbers_nat := pow_numbers_nat
  pow_numbers_int := pow_numbers_int
  add_closed := add_closed
  div_closed := div_closed

end Litex.NumericModel


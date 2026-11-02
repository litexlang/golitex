import Litex.ElementaryFunctions

universe u

namespace Litex

theorem realPartOfRealValue {M : Semantics.{u}} (a : M.Value)
    (ha : M.mem a (M.standard .real)) :
    complexUnaryValue (fun z : ℂ => (z.re : ℂ)) a = a := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  rw [hr, complexUnaryValue_number, Complex.ofReal_re]

theorem imaginaryPartOfRealValue {M : Semantics.{u}} (a : M.Value)
    (ha : M.mem a (M.standard .real)) :
    complexUnaryValue (fun z : ℂ => (z.im : ℂ)) a = M.number 0 := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  rw [hr, complexUnaryValue_number, Complex.ofReal_im, Complex.ofReal_zero]

theorem realPartRectangularValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (realFirst unitFirst : Bool) :
    complexUnaryValue (fun z : ℂ => (z.re : ℂ))
      (if realFirst then M.addValue a
        (if unitFirst then M.mulValue (M.number Complex.I) b else M.mulValue b (M.number Complex.I))
      else M.addValue
        (if unitFirst then M.mulValue (M.number Complex.I) b else M.mulValue b (M.number Complex.I)) a) = a := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  obtain ⟨s, hs⟩ := (M.real_members _).mp hb
  rw [hr, hs]
  cases realFirst <;> cases unitFirst <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.add_numbers, M.mul_numbers,
      complexUnaryValue_number, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, zero_add, add_zero]

theorem imaginaryPartRectangularValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (realFirst unitFirst : Bool) :
    complexUnaryValue (fun z : ℂ => (z.im : ℂ))
      (if realFirst then M.addValue a
        (if unitFirst then M.mulValue (M.number Complex.I) b else M.mulValue b (M.number Complex.I))
      else M.addValue
        (if unitFirst then M.mulValue (M.number Complex.I) b else M.mulValue b (M.number Complex.I)) a) = b := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  obtain ⟨s, hs⟩ := (M.real_members _).mp hb
  rw [hr, hs]
  cases realFirst <;> cases unitFirst <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.add_numbers, M.mul_numbers,
      complexUnaryValue_number, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, one_mul, mul_one, zero_add, add_zero]

theorem complexRealProduct (a b : ℂ) :
    ((a * b).re : ℂ) = (a.re : ℂ) * (b.re : ℂ) - (a.im : ℂ) * (b.im : ℂ) := by
  rw [Complex.mul_re, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul]

theorem complexImaginaryProduct (a b : ℂ) :
    ((a * b).im : ℂ) = (a.re : ℂ) * (b.im : ℂ) + (a.im : ℂ) * (b.re : ℂ) := by
  rw [Complex.mul_im, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul]

end Litex

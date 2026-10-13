import examples.rational_inverse_maps.statement
import rational_inverse_maps.RationalMaps

namespace Adapter

private noncomputable abbrev model := Litex.NumericModel.model
private noncomputable abbrev forwardFunction := LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit._object_i4 (M := model)
private noncomputable abbrev backwardFunction := LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit._object_i7 (M := model)

private theorem encodeDistinct (x y : ℚ) (h : x ≠ y) :
    ¬ Litex.Same (Litex.number (M := model) (x : ℂ)) (Litex.number (y : ℂ)) :=
  fun same => h (Rat.cast_injective (Litex.NativeBridge.complexEq same))

private noncomputable def forwardCall {α : Type*} [Litex.Representation model α]
    (a : Litex.Obj (M := model) α) (ha : Litex.In a Litex.Q)
    (h1 : ¬ Litex.Same a (Litex.number 1)) :=
  Litex.call .rational .rational (fun raw => raw ≠ model.number 1) forwardFunction a
    (LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit.h_627 (M := model)) ha h1

private noncomputable def backwardCall {α : Type*} [Litex.Representation model α]
    (a : Litex.Obj (M := model) α) (ha : Litex.In a Litex.Q)
    (h2 : ¬ Litex.Same a (Litex.number 2)) :=
  Litex.call .rational .rational (fun raw => raw ≠ model.number 2) backwardFunction a
    (LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit.h_1038 (M := model)) ha h2

private theorem forwardCallDenote {α : Type*} [Litex.Representation model α]
    (a : Litex.Obj (M := model) α) (ha : Litex.In a Litex.Q)
    (h1 : ¬ Litex.Same a (Litex.number 1))
    (x : ℚ) (hx : x ≠ 1) (hvalue : Litex.denote a = model.number (x : ℂ)) :
    Litex.denote (forwardCall a ha h1) = model.number (RationalMaps.forward x : ℂ) := by
  have hd : model.mem (Litex.denote a) forwardFunction.val.signature.domain :=
    (Litex.FunctionSignature.one_domain .rational .rational (fun raw => raw ≠ model.number 1) _).mpr ⟨ha, h1⟩
  have beta := Litex.FunctionSemantics.call_graphValue
    forwardFunction.val.signature.domain forwardFunction.val.signature.target
    forwardFunction.val.bodyValue forwardFunction.wd (Litex.denote a) hd
  change Litex.denote (forwardCall a ha h1) =
    model.divValue (model.addValue (model.mulValue (model.number 2) (Litex.denote a)) (model.number 1))
      (model.subValue (Litex.denote a) (model.number 1)) at beta
  have hxC : (x : ℂ) ≠ 1 := fun h => hx (Rat.cast_injective (by simpa only [Rat.cast_one] using h))
  rw [hvalue, model.mul_numbers, model.add_numbers, model.sub_numbers,
    model.div_numbers _ _ (sub_ne_zero.mpr hxC)] at beta
  simpa only [RationalMaps.forward, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] using beta

private theorem backwardCallDenote {α : Type*} [Litex.Representation model α]
    (a : Litex.Obj (M := model) α) (ha : Litex.In a Litex.Q)
    (h2 : ¬ Litex.Same a (Litex.number 2))
    (y : ℚ) (hy : y ≠ 2) (hvalue : Litex.denote a = model.number (y : ℂ)) :
    Litex.denote (backwardCall a ha h2) = model.number (RationalMaps.backward y : ℂ) := by
  have hd : model.mem (Litex.denote a) backwardFunction.val.signature.domain :=
    (Litex.FunctionSignature.one_domain .rational .rational (fun raw => raw ≠ model.number 2) _).mpr ⟨ha, h2⟩
  have beta := Litex.FunctionSemantics.call_graphValue
    backwardFunction.val.signature.domain backwardFunction.val.signature.target
    backwardFunction.val.bodyValue backwardFunction.wd (Litex.denote a) hd
  change Litex.denote (backwardCall a ha h2) =
    model.divValue (model.addValue (Litex.denote a) (model.number 1))
      (model.subValue (Litex.denote a) (model.number 2)) at beta
  have hyC : (y : ℂ) ≠ 2 := fun h => hy (Rat.cast_injective h)
  rw [hvalue, model.add_numbers, model.sub_numbers,
    model.div_numbers _ _ (sub_ne_zero.mpr hyC)] at beta
  simpa only [RationalMaps.backward, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
    Rat.cast_ofNat, Rat.cast_one] using beta

theorem forwardPreservesDomain (x : ℚ) (hx : x ≠ 1) :
    RationalMaps.forward x ≠ 2 := by
  let a := Litex.number (M := model) (x : ℂ)
  have ha := Litex.NativeBridge.numberInQ (M := model) x
  have hguard : ¬ Litex.Same a (Litex.number 1) := by
    simpa only [Rat.cast_one, Rat.cast_ofNat] using encodeDistinct x 1 hx
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit.h_1042 (M := model) a ha hguard
  have observed := forwardCallDenote a ha hguard x hx rfl
  intro equal
  apply generated
  change Litex.denote (forwardCall a ha hguard) = model.number 2
  rw [observed]
  simpa only [Rat.cast_one, Rat.cast_ofNat] using congrArg (fun y : ℚ => model.number (y : ℂ)) equal

theorem backwardPreservesDomain (x : ℚ) (hx : x ≠ 2) :
    RationalMaps.backward x ≠ 1 := by
  let a := Litex.number (M := model) (x : ℂ)
  have ha := Litex.NativeBridge.numberInQ (M := model) x
  have hguard : ¬ Litex.Same a (Litex.number 2) := by
    simpa only [Rat.cast_one, Rat.cast_ofNat] using encodeDistinct x 2 hx
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit.h_5990 (M := model) a ha hguard
  have observed := backwardCallDenote a ha hguard x hx rfl
  intro equal
  apply generated
  change Litex.denote (backwardCall a ha hguard) = model.number 1
  rw [observed]
  simpa only [Rat.cast_one, Rat.cast_ofNat] using congrArg (fun y : ℚ => model.number (y : ℂ)) equal

theorem leftInverse (x : ℚ) (hx : x ≠ 1) :
    RationalMaps.backward (RationalMaps.forward x) = x := by
  let a := Litex.number (M := model) (x : ℂ)
  have ha := Litex.NativeBridge.numberInQ (M := model) x
  have h1 : ¬ Litex.Same a (Litex.number 1) := by
    simpa only [Rat.cast_one, Rat.cast_ofNat] using encodeDistinct x 1 hx
  have hf : ¬ Litex.Same (forwardCall a ha h1) (Litex.number 2) :=
    LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit.h_1042 (M := model) a ha h1
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit.h_10318 (M := model) a ha h1
  have first := forwardCallDenote a ha h1 x hx rfl
  have both := backwardCallDenote (forwardCall a ha h1) (Litex.callInOutput _) hf
    (RationalMaps.forward x) (forwardPreservesDomain x hx) first
  change Litex.denote (backwardCall (forwardCall a ha h1) (Litex.callInOutput _) hf) = model.number (x : ℂ) at generated
  exact Rat.cast_injective (model.number_injective (both.symm.trans generated))

theorem rightInverse (y : ℚ) (hy : y ≠ 2) :
    RationalMaps.forward (RationalMaps.backward y) = y := by
  let b := Litex.number (M := model) (y : ℂ)
  have hb := Litex.NativeBridge.numberInQ (M := model) y
  have h2 : ¬ Litex.Same b (Litex.number 2) := by
    simpa only [Rat.cast_one, Rat.cast_ofNat] using encodeDistinct y 2 hy
  have hf : ¬ Litex.Same (backwardCall b hb h2) (Litex.number 1) :=
    LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit.h_5990 (M := model) b hb h2
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit.h_21048 (M := model) b hb h2
  have first := backwardCallDenote b hb h2 y hy rfl
  have both := forwardCallDenote (backwardCall b hb h2) (Litex.callInOutput _) hf
    (RationalMaps.backward y) (backwardPreservesDomain y hy) first
  change Litex.denote (forwardCall (backwardCall b hb h2) (Litex.callInOutput _) hf) = model.number (y : ℂ) at generated
  exact Rat.cast_injective (model.number_injective (both.symm.trans generated))

theorem forwardInjective (a b : ℚ) (ha : a ≠ 1) (hb : b ≠ 1)
    (equal : RationalMaps.forward a = RationalMaps.forward b) : a = b := by
  let x := Litex.number (M := model) (a : ℂ)
  let y := Litex.number (M := model) (b : ℂ)
  have hx := Litex.NativeBridge.numberInQ (M := model) a
  have hy := Litex.NativeBridge.numberInQ (M := model) b
  have hx1 : ¬ Litex.Same x (Litex.number 1) := by
    simpa only [Rat.cast_one, Rat.cast_ofNat] using encodeDistinct a 1 ha
  have hy1 : ¬ Litex.Same y (Litex.number 1) := by
    simpa only [Rat.cast_one, Rat.cast_ofNat] using encodeDistinct b 1 hb
  have first := forwardCallDenote x hx hx1 a ha rfl
  have last := forwardCallDenote y hy hy1 b hb rfl
  have heq : Litex.Same (forwardCall x hx hx1) (forwardCall y hy hy1) :=
    first.trans ((congrArg (fun q : ℚ => model.number (q : ℂ)) equal).trans last.symm)
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit.h_37256 (M := model) x hx y hy hx1 hy1 heq
  exact Rat.cast_injective (model.number_injective generated)

end Adapter

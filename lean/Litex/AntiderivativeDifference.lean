import Litex.AntiderivativeAlgebra

universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem antiderivativeDifferenceConstantInterval
    (first second function a b base : M.Value)
    (realFirst : RealFunctionValue M first) (realSecond : RealFunctionValue M second)
    (realA : M.mem a (M.standard .real)) (realB : M.mem b (M.standard .real))
    (coverFirst : ∀ x, M.mem x (F.sepValue (M.standard .real)
      (fun x => realBound false a x ∧ realBound false x b)) → M.mem x (F.domainValue first))
    (coverSecond : ∀ x, M.mem x (F.sepValue (M.standard .real)
      (fun x => realBound false a x ∧ realBound false x b)) → M.mem x (F.domainValue second))
    (baseMember : M.mem base (F.sepValue (M.standard .real)
      (fun x => realBound false a x ∧ realBound false x b)))
    (sourceFirst : IsAntiderivativeOnValue M first function (F.sepValue (M.standard .real)
      (fun x => realBound false a x ∧ realBound false x b)))
    (sourceSecond : IsAntiderivativeOnValue M second function (F.sepValue (M.standard .real)
      (fun x => realBound false a x ∧ realBound false x b))) :
    ∀ x, M.mem x (F.sepValue (M.standard .real)
      (fun x => realBound false a x ∧ realBound false x b)) →
      M.subValue (F.callValue first x) (F.callValue second x)=
      M.subValue (F.callValue first base) (F.callValue second base) := by
  obtain ⟨ar,rfl⟩ := (M.real_members a).mp realA
  obtain ⟨br,rfl⟩ := (M.real_members b).mp realB
  let region := F.sepValue (M.standard .real)
    (fun x => realBound false (M.number (ar : ℂ)) x ∧ realBound false x (M.number (br : ℂ)))
  have member (x : ℝ) (hx : x ∈ Set.Ioo ar br) : M.mem (M.number (x : ℂ)) region :=
    (F.sep_members _ _ _).mpr ⟨(M.real_members _).mpr ⟨x,rfl⟩,
      ⟨ar,x,rfl,rfl,hx.1⟩,⟨x,br,rfl,rfl,hx.2⟩⟩
  have nativeMember (x : ℝ) (hx : M.mem (M.number (x : ℂ)) region) : x ∈ Set.Ioo ar br := by
    obtain ⟨_,left,right⟩ := (F.sep_members _ _ _).mp hx
    exact ⟨(realLtValue_numbers _ _).mp left,(realLtValue_numbers _ _).mp right⟩
  have derivative (x : ℝ) (hx : x ∈ Set.Ioo ar br) :
      HasDerivAt (fun y => observeRealFunction first y-observeRealFunction second y) 0 x := by
    obtain ⟨p,d,hp,hd,hi,he⟩ := sourceFirst _ (member x hx)
    have px : p=x := (Complex.ofReal_injective (M.number_injective hp)).symm
    subst p
    obtain ⟨q,e,hq,hvalue,hinterior,hcontrol⟩ := sourceSecond _ (member x hx)
    have qx : q=x := (Complex.ofReal_injective (M.number_injective hq)).symm
    subst q
    have values : d=e := Complex.ofReal_injective (M.number_injective (hd.symm.trans hvalue))
    have hfirst := (derivativeEpsilon_iff_hasDerivAt first x d hi).mp he
    have hsecond := (derivativeEpsilon_iff_hasDerivAt second x e hinterior).mp hcontrol
    have difference := hfirst.sub hsecond
    rw [values,sub_self] at difference
    exact difference
  obtain ⟨baseReal,baseEqual⟩ := (M.real_members base).mp ((F.sep_members _ _ _).mp baseMember).1
  have baseNative : baseReal ∈ Set.Ioo ar br := nativeMember baseReal (by rwa [←baseEqual])
  intro x hx
  obtain ⟨point,pointEqual⟩ := (M.real_members x).mp ((F.sep_members _ _ _).mp hx).1
  have pointNative : point ∈ Set.Ioo ar br := nativeMember point (by rwa [←pointEqual])
  have same : observeRealFunction first point-observeRealFunction second point=
      observeRealFunction first baseReal-observeRealFunction second baseReal :=
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo ar br).isPreconnected
      (fun y hy => (derivative y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (derivative y hy).deriv) pointNative baseNative
  rw [pointEqual,baseEqual]
  rw [observeRealFunction_spec first realFirst point (coverFirst _ (by rwa [←pointEqual])),
    observeRealFunction_spec second realSecond point (coverSecond _ (by rwa [←pointEqual])),
    observeRealFunction_spec first realFirst baseReal (coverFirst _ (by rwa [←baseEqual])),
    observeRealFunction_spec second realSecond baseReal (coverSecond _ (by rwa [←baseEqual])),
    M.sub_numbers,M.sub_numbers,←Complex.ofReal_sub,←Complex.ofReal_sub,same]
end Litex

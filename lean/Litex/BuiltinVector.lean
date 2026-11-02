import Litex.Matrices
import Litex.BuiltinComplex
import Litex.Multivariable
universe u v w x
namespace Litex

theorem finiteInnerProductSelfPositive {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ))
    (hself : Same p.val.left p.val.right) : In p R ∧ Le (number 0) p := by
  let q := euclideanNorm p.val.left p.val.dimension p.wd.1 p.wd.2.1
  have heq : denote p = M.number (euclideanNormSum (denote p.val.left) p.val.dimension) := by
    change M.number (finiteInnerProductValue (denote p.val.left) (denote p.val.right) p.val.dimension) = _
    change denote p.val.left = denote p.val.right at hself
    rw [← hself]
    exact (euclideanNormSquareInner q).symm.trans (euclideanNormSquare q)
  obtain ⟨r,hr,hsum⟩ := finiteMagnitudeSquareSumNonnegative
    (matrixIndexValue p.val.dimension)
    (fun k => NativeBridge.complexValue (F.callValue (denote p.val.left) k))
    (matrixIndexFinite p.val.dimension p.wd.1)
  have hvalue : denote p = M.number (r : ℂ) := heq.trans (congrArg M.number hsum)
  exact ⟨(M.real_members _).mpr ⟨r,hvalue⟩, 0,r,rfl,hvalue,hr⟩

theorem finiteInnerProductLinearRightValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (u v w c a b : M.Value) (n : Obj (M := M) α) (hn : In n N)
    (hu : M.mem u (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hv : M.mem v (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hw : M.mem w (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (ha : M.mem a (M.standard .complex)) (hb : M.mem b (M.standard .complex))
    (hlin : ∀ k, M.mem k (matrixIndexValue n) → F.callValue c k =
      M.addValue (M.mulValue a (F.callValue v k)) (M.mulValue b (F.callValue w k))) :
    M.number (finiteInnerProductValue u c n) =
      M.addValue (M.mulValue a (M.number (finiteInnerProductValue u v n)))
        (M.mulValue b (M.number (finiteInnerProductValue u w n))) := by
  obtain ⟨ar,har⟩ := (M.complex_members _).mp ha
  obtain ⟨br,hbr⟩ := (M.complex_members _).mp hb
  rw [har,hbr,M.mul_numbers,M.mul_numbers,M.add_numbers]
  apply congrArg M.number
  unfold finiteInnerProductValue
  have finite := matrixIndexFinite n hn
  calc
    _ = finiteAggregateValue false (matrixIndexValue n)
        (fun k => ar * NativeBridge.complexValue (finiteInnerProductTerm u v k) +
          br * NativeBridge.complexValue (finiteInnerProductTerm u w k)) := by
      apply finiteAggregateValue_congr
      intro k hk
      have hd : M.mem k (finiteSeqDomain n) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
      obtain ⟨ur,hur⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ hu hd)
      obtain ⟨vr,hvr⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ hv hd)
      obtain ⟨wr,hwr⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ hw hd)
      simp only [finiteInnerProductTerm,hlin k hk,har,hbr,hur,hvr,hwr,
        complexUnaryValue_number,M.mul_numbers,M.add_numbers,NativeBridge.complexValue_number]
      ring
    _ = _ := by
      rw [finiteSumValueAdd _ _ _ finite,finiteSumValueMulLeft _ ar _ finite,
        finiteSumValueMulLeft _ br _ finite]
      rfl

theorem finiteInnerProductLinearRight {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ))
    (g : Obj (M := M) (FormulaFn M)) (v w a b : M.Value)
    (hv : M.mem v (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .complex)))
    (hw : M.mem w (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .complex)))
    (ha : M.mem a (M.standard .complex)) (hb : M.mem b (M.standard .complex))
    (hg : Same p.val.right g) (hD : g.val.signature.domain = finiteSeqDomain p.val.dimension)
    (hbody : g.val.bodyValue = fun k =>
      M.addValue (M.mulValue a (F.callValue v k)) (M.mulValue b (F.callValue w k))) :
    denote p = M.addValue (M.mulValue a (M.number
      (finiteInnerProductValue (denote p.val.left) v p.val.dimension)))
      (M.mulValue b (M.number (finiteInnerProductValue (denote p.val.left) w p.val.dimension))) := by
  apply finiteInnerProductLinearRightValue _ _ _ _ _ _ _ p.wd.1 p.wd.2.1 hv hw ha hb
  intro k hk
  have hd : M.mem k g.val.signature.domain := hD.symm ▸ (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  change denote p.val.right = denote g at hg
  rw [hg]
  exact (FunctionSemantics.call_graphValue _ _ _ g.wd k hd).trans (congrFun hbody k)

theorem euclideanNormScaleValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (a v c : M.Value) (n : Obj (M := M) α) (hn : In n N)
    (ha : M.mem a (M.standard .complex))
    (hv : M.mem v (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hscale : ∀ k, M.mem k (matrixIndexValue n) →
      F.callValue c k = M.mulValue a (F.callValue v k)) :
    sqrtValue (M.number (euclideanNormSum c n)) =
      M.mulValue (complexUnaryValue (fun z : ℂ => (‖z‖ : ℂ)) a)
        (sqrtValue (M.number (euclideanNormSum v n))) := by
  obtain ⟨ar,har⟩ := (M.complex_members _).mp ha
  have hs : euclideanNormSum c n = (‖ar‖ ^ 2 : ℝ) * euclideanNormSum v n := by
    unfold euclideanNormSum
    calc
      _ = finiteAggregateValue false (matrixIndexValue n)
          (fun k => ((‖ar‖ ^ 2 : ℝ) : ℂ) * ((‖NativeBridge.complexValue (F.callValue v k)‖ ^ 2 : ℝ) : ℂ)) := by
        apply finiteAggregateValue_congr
        intro k hk
        have hd : M.mem k (finiteSeqDomain n) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
        obtain ⟨vr,hvr⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ hv hd)
        simp only [hscale k hk,har,hvr,M.mul_numbers,NativeBridge.complexValue_number,
          norm_mul,mul_pow,Complex.ofReal_mul]
      _ = _ := finiteSumValueMulLeft _ _ _ (matrixIndexFinite n hn)
  obtain ⟨r,hr,heq⟩ := finiteMagnitudeSquareSumNonnegative (matrixIndexValue n)
    (fun k => NativeBridge.complexValue (F.callValue v k)) (matrixIndexFinite n hn)
  change euclideanNormSum v n = (r : ℂ) at heq
  rw [hs,heq,← Complex.ofReal_mul,sqrtValue_number,sqrtValue_number,har,
    complexUnaryValue_number,M.mul_numbers]
  apply congrArg M.number
  rw [Real.sqrt_mul (sq_nonneg ‖ar‖),Real.sqrt_sq (norm_nonneg ar),Complex.ofReal_mul]

theorem euclideanNormScale {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β))
    (g : Obj (M := M) (FormulaFn M)) (a v : M.Value)
    (ha : M.mem a (M.standard .complex))
    (hv : M.mem v (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .complex)))
    (hg : Same p.val.vector g)
    (hD : g.val.signature.domain = finiteSeqDomain p.val.dimension)
    (hb : g.val.bodyValue = fun k => M.mulValue a (F.callValue v k)) :
    denote p = M.mulValue (complexUnaryValue (fun z : ℂ => (‖z‖ : ℂ)) a)
      (sqrtValue (M.number (euclideanNormSum v p.val.dimension))) := by
  apply euclideanNormScaleValue _ _ _ _ p.wd.1 ha hv
  intro k hk
  have hd : M.mem k g.val.signature.domain := hD.symm ▸ (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  change denote p.val.vector = denote g at hg
  rw [hg]
  exact (FunctionSemantics.call_graphValue _ _ _ g.wd k hd).trans (congrFun hb k)
end Litex

import Litex.Multivariable
universe u v w x
namespace Litex

theorem finiteMagnitudeSquareSumZero {M : Semantics.{u}} (A : M.Value)
    (f : M.Value → ℂ) (hf : (memberSet A).Finite) :
    finiteAggregateValue false A (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) = 0 ↔
      ∀ x, M.mem x A → f x = 0 := by
  classical
  have hsum : finiteAggregateValue false A (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) =
      ((∑ x ∈ hf.toFinset, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    simp only [finiteAggregateValue, dif_pos hf, Bool.false_eq_true, ↓reduceIte]
    exact (map_sum Complex.ofRealHom (fun x => ‖f x‖ ^ 2) hf.toFinset).symm
  rw [hsum,Complex.ofReal_eq_zero]
  constructor
  · intro zero x hx
    have allZero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y (_ : y ∈ hf.toFinset) => sq_nonneg (‖f y‖))).mp zero
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (allZero x (hf.mem_toFinset.mpr hx)))
  · intro zero
    apply Finset.sum_eq_zero
    intro x hx
    rw [zero x (hf.mem_toFinset.mp hx),norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]

theorem euclideanNormZeroEntries {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type _} {β : Type _} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) :
    Same p (number 0) ↔ ∀ k, M.mem k (finiteSeqDomain p.val.dimension) →
      F.callValue (denote p.val.vector) k = M.number 0 := by
  let g := fun k => NativeBridge.complexValue (F.callValue (denote p.val.vector) k)
  have finite := matrixIndexFinite p.val.dimension p.wd.1
  constructor
  · intro zero
    have square := euclideanNormSquare p
    change M.powValue (denote p) (M.number ((2 : ℕ) : ℂ)) = _ at square
    rw [zero] at square
    change M.powValue (M.number 0) (M.number ((2 : ℕ) : ℂ)) = _ at square
    rw [M.pow_numbers_nat,zero_pow (by decide : (2 : ℕ) ≠ 0)] at square
    have sumZero : euclideanNormSum (denote p.val.vector) p.val.dimension = 0 :=
      M.number_injective square.symm
    have entries := (finiteMagnitudeSquareSumZero (matrixIndexValue p.val.dimension) g finite).mp sumZero
    intro k hk
    have entry := entries k ((F.sep_members _ _ _).mp hk).1
    exact (NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ p.wd.2 hk)).trans
      (congrArg M.number entry)
  · intro entries
    have sumZero : euclideanNormSum (denote p.val.vector) p.val.dimension = 0 := by
      apply (finiteMagnitudeSquareSumZero (matrixIndexValue p.val.dimension) g finite).mpr
      intro k hk
      unfold g
      rw [entries k ((F.sep_members _ _ _).mpr ⟨hk,True.intro⟩),NativeBridge.complexValue_number]
    change sqrtValue (M.number (euclideanNormSum _ _)) = M.number 0
    rw [sumZero]
    change sqrtValue (M.number ((0 : ℝ) : ℂ)) = M.number 0
    rw [sqrtValue_number,Real.sqrt_zero,Complex.ofReal_zero]

theorem euclideanNormZeroCharacterization {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (zero : Obj (M := M) γ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hz : M.mem (denote zero) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (calls : ∀ k, M.mem k (finiteSeqDomain n) → F.callValue (denote zero) k = M.number 0) :
    (Same (euclideanNorm a n hn ha) (number 0) → Same a zero) ∧
    (Same a zero → Same (euclideanNorm a n hn ha) (number 0)) := by
  constructor
  · intro normZero
    have entries := (euclideanNormZeroEntries (euclideanNorm a n hn ha)).mp normZero
    apply functionExtOnDomain a zero (matrixApplySignature n .complex)
      (matrixApplySignature n .complex) ha hz rfl
    intro k hk
    exact (entries k hk).trans (calls k hk).symm
  · intro same
    apply (euclideanNormZeroEntries (euclideanNorm a n hn ha)).mpr
    intro k hk
    change F.callValue (denote a) k = M.number 0
    rw [same]
    exact calls k hk

theorem finiteRealSumZero {M : Semantics.{u}} (A : M.Value)
    (f : M.Value → ℝ) (hf : (memberSet A).Finite)
    (nonnegative : ∀ x, M.mem x A → 0 ≤ f x) :
    finiteAggregateValue false A (fun x => (f x : ℂ)) = 0 ↔
      ∀ x, M.mem x A → f x = 0 := by
  classical
  have hsum : finiteAggregateValue false A (fun x => (f x : ℂ)) =
      ((∑ x ∈ hf.toFinset, f x : ℝ) : ℂ) := by
    simp only [finiteAggregateValue,dif_pos hf,Bool.false_eq_true,↓reduceIte]
    exact (map_sum Complex.ofRealHom f hf.toFinset).symm
  rw [hsum,Complex.ofReal_eq_zero]
  constructor
  · intro h x hx
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun y hy => nonnegative y (hf.mem_toFinset.mp hy))).mp h x (hf.mem_toFinset.mpr hx)
  · intro h
    exact Finset.sum_eq_zero (fun x hx => h x (hf.mem_toFinset.mp hx))

theorem finiteNestedMagnitudeSquareSumZero {M : Semantics.{u}}
    (A B : M.Value) (f : M.Value → M.Value → ℂ)
    (ha : (memberSet A).Finite) (hb : (memberSet B).Finite) :
    finiteAggregateValue false A (fun x => finiteAggregateValue false B
      (fun y => ((‖f x y‖ ^ 2 : ℝ) : ℂ))) = 0 ↔
      ∀ x, M.mem x A → ∀ y, M.mem y B → f x y = 0 := by
  classical
  let inner := fun x => ∑ y ∈ hb.toFinset, ‖f x y‖ ^ 2
  have hinner : ∀ x, finiteAggregateValue false B (fun y => ((‖f x y‖ ^ 2 : ℝ) : ℂ)) = (inner x : ℂ) := by
    intro x
    simp only [finiteAggregateValue,dif_pos hb,Bool.false_eq_true,↓reduceIte]
    exact (map_sum Complex.ofRealHom (fun y => ‖f x y‖ ^ 2) hb.toFinset).symm
  have outer := finiteAggregateValue_congr false A _ _ (fun x _ => hinner x)
  rw [outer,finiteRealSumZero A inner ha (fun x _ => Finset.sum_nonneg (fun y _ => sq_nonneg (‖f x y‖)))]
  constructor
  · intro h x hx
    apply (finiteMagnitudeSquareSumZero B (f x) hb).mp
    rw [hinner,h x hx,Complex.ofReal_zero]
  · intro h x hx
    have zero := (finiteMagnitudeSquareSumZero B (f x) hb).mpr (h x hx)
    rw [hinner] at zero
    exact Complex.ofReal_eq_zero.mp zero

theorem frobeniusNormZeroEntries {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) :
    Same p (number 0) ↔ ∀ r, M.mem r (matrixIndexValue p.val.rows) →
      ∀ c, M.mem c (matrixIndexValue p.val.cols) →
        F.callValue (denote p.val.matrix) (FiniteFunction.pack2 r c) = M.number 0 := by
  let g := fun r c => NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 r c))
  have hm := matrixIndexFinite p.val.rows p.wd.1
  have hn := matrixIndexFinite p.val.cols p.wd.2.1
  constructor
  · intro zero
    have square := frobeniusNormSquare p
    rw [zero] at square
    change M.powValue (M.number 0) (M.number ((2 : ℕ) : ℂ)) = _ at square
    rw [M.pow_numbers_nat,zero_pow (by decide : (2 : ℕ) ≠ 0)] at square
    have sumZero : frobeniusNormSum (denote p.val.matrix) p.val.rows p.val.cols = 0 :=
      M.number_injective square.symm
    have entries := (finiteNestedMagnitudeSquareSumZero _ _ g hm hn).mp sumZero
    intro r hr c hc
    have member := matrixDomain_pair p.val.rows p.val.cols r c hr hc
    exact (NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ p.wd.2.2 member)).trans
      (congrArg M.number (entries r hr c hc))
  · intro entries
    have sumZero : frobeniusNormSum (denote p.val.matrix) p.val.rows p.val.cols = 0 := by
      apply (finiteNestedMagnitudeSquareSumZero _ _ g hm hn).mpr
      intro r hr c hc
      unfold g
      rw [entries r hr c hc,NativeBridge.complexValue_number]
    change sqrtValue (M.number (frobeniusNormSum _ _ _)) = M.number 0
    rw [sumZero]
    change sqrtValue (M.number ((0 : ℝ) : ℂ)) = M.number 0
    rw [sqrtValue_number,Real.sqrt_zero,Complex.ofReal_zero]

theorem frobeniusNormZeroCharacterization {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    (Same (frobeniusNorm a m n hm hn ha) (number 0) → Same a (zeroMatrix m n hm hn)) ∧
    (Same a (zeroMatrix m n hm hn) → Same (frobeniusNorm a m n hm hn ha) (number 0)) := by
  constructor
  · intro normZero
    have entries := (frobeniusNormZeroEntries (frobeniusNorm a m n hm hn ha)).mp normZero
    apply matrixSameOfComplexEntries a (zeroMatrix m n hm hn) m n ha
      (functionRealToComplex (zeroMatrixInFnSet (zeroMatrix m n hm hn)))
    intro r c hr hc
    have entry := entries r hr c hc
    change F.callValue (denote a) (FiniteFunction.pack2 r c) = M.number 0 at entry
    exact congrArg NativeBridge.complexValue (entry.trans
      (zeroMatrixCall (zeroMatrix m n hm hn) (FiniteFunction.pack2 r c)
        (matrixDomain_pair m n r c hr hc)).symm)
  · intro same
    apply (frobeniusNormZeroEntries (frobeniusNorm a m n hm hn ha)).mpr
    intro r hr c hc
    change F.callValue (denote a) (FiniteFunction.pack2 r c) = M.number 0
    rw [same]
    exact zeroMatrixCall (zeroMatrix m n hm hn) (FiniteFunction.pack2 r c)
      (matrixDomain_pair m n r c hr hc)

theorem euclideanNormZeroFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β)
    (zero : Obj (M := M) (FormulaFn M)) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (domain : zero.val.signature.domain = finiteSeqDomain n)
    (target : zero.val.signature.target = M.standard .complex)
    (body : ∀ k, zero.val.bodyValue k = M.number 0) :
    (Same (euclideanNorm a n hn ha) (number 0) → Same a zero) ∧
    (Same a zero → Same (euclideanNorm a n hn ha) (number 0)) := by
  have hz := formulaFnInFnSet zero
  change M.mem (denote zero) (F.fnSetValue zero.val.signature.domain zero.val.signature.target) at hz
  rw [domain,target] at hz
  apply euclideanNormZeroCharacterization a n zero hn ha hz
  intro k hk
  change F.callValue (F.graphValue _ _ _) k = M.number 0
  exact (F.call_graphValue _ _ _ zero.wd k (domain.symm ▸ hk)).trans (body k)

end Litex

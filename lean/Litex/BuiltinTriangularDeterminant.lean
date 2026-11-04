import Litex.Multivariable
universe u v w
namespace Litex

theorem finiteProductMatrixIndex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N)
    (f : M.Value → ℂ) :
    finiteAggregateValue true (matrixIndexValue n) f =
      ∏ i : Fin (NativeBridge.naturalValue (denote n)), f (FiniteFunction.index i) := by
  classical
  have hf := matrixIndexFinite n hn
  simp only [finiteAggregateValue,dif_pos hf,↓reduceIte]
  symm
  apply Finset.prod_bij (fun i _ => FiniteFunction.index i)
  · intro i _
    exact hf.mem_toFinset.mpr (matrixIndexOfFin n hn i)
  · intro i _ j _ same
    exact FiniteFunction.index_injective same
  · intro value hv
    obtain ⟨i,hi⟩ := matrixIndexExistsFin n hn value (hf.mem_toFinset.mp hv)
    exact ⟨i,Finset.mem_univ _,hi.symm⟩
  · intro i _
    rfl

theorem finiteIndexRealLt {M : Semantics.{u}} {n : ℕ} (a b : Fin n) (h : a < b) :
    RealLtValue M (FiniteFunction.index a) (FiniteFunction.index b) := by
  change RealLtValue M (M.number ((a.val+1 : ℕ) : ℂ)) (M.number ((b.val+1 : ℕ) : ℂ))
  have comparison : ((a.val+1 : ℕ) : ℝ) < ((b.val+1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ h
  simpa only [Complex.ofReal_natCast] using
    (realLtValue_numbers (M := M) ((a.val+1 : ℕ) : ℝ) ((b.val+1 : ℕ) : ℝ)).mpr comparison

theorem matrixDeterminantUpperTriangularValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (_ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (zero : ∀ r, M.mem r (matrixIndexValue n) → ∀ c, M.mem c (matrixIndexValue n) →
      RealLtValue M c r → F.callValue (denote a) (FiniteFunction.pack2 r c) = M.number 0) :
    matrixDeterminantValue (denote a) n = M.number
      (finiteAggregateValue true (matrixIndexValue n)
        (fun k => NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 k k)))) := by
  let A := matrixComplexValue (denote a) n n
  have triangular : A.BlockTriangular id := by
    intro r c less
    change NativeBridge.complexValue (F.callValue (denote a)
      (FiniteFunction.pack2 (FiniteFunction.index r) (FiniteFunction.index c))) = 0
    rw [zero _ (matrixIndexOfFin n hn r) _ (matrixIndexOfFin n hn c) (finiteIndexRealLt c r less),
      NativeBridge.complexValue_number]
  change M.number A.det = _
  apply congrArg M.number
  exact (Matrix.det_of_upperTriangular triangular).trans (finiteProductMatrixIndex n hn (fun k => NativeBridge.complexValue
    (F.callValue (denote a) (FiniteFunction.pack2 k k)))).symm

theorem matrixDeterminantLowerTriangularValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (_ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (zero : ∀ r, M.mem r (matrixIndexValue n) → ∀ c, M.mem c (matrixIndexValue n) →
      RealLtValue M r c → F.callValue (denote a) (FiniteFunction.pack2 r c) = M.number 0) :
    matrixDeterminantValue (denote a) n = M.number
      (finiteAggregateValue true (matrixIndexValue n)
        (fun k => NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 k k)))) := by
  let A := matrixComplexValue (denote a) n n
  have triangular : A.BlockTriangular OrderDual.toDual := by
    intro r c less
    change NativeBridge.complexValue (F.callValue (denote a)
      (FiniteFunction.pack2 (FiniteFunction.index r) (FiniteFunction.index c))) = 0
    rw [zero _ (matrixIndexOfFin n hn r) _ (matrixIndexOfFin n hn c) (finiteIndexRealLt r c less),
      NativeBridge.complexValue_number]
  change M.number A.det = _
  apply congrArg M.number
  exact (Matrix.det_of_lowerTriangular A triangular).trans (finiteProductMatrixIndex n hn (fun k => NativeBridge.complexValue
    (F.callValue (denote a) (FiniteFunction.pack2 k k)))).symm

theorem finiteDiagonalProductFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (g : Obj (M := M) (FormulaFn M))
    (domain : g.val.signature.domain = finiteSeqDomain n)
    (body : g.val.bodyValue = fun k => F.callValue (denote a) (FiniteFunction.pack2 k k)) :
    finiteAggregateValue true (matrixIndexValue n)
      (fun k => NativeBridge.complexValue (F.callValue (denote g) k)) =
    finiteAggregateValue true (matrixIndexValue n)
      (fun k => NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 k k))) := by
  apply finiteAggregateValue_congr
  intro k hk
  have member : M.mem k g.val.signature.domain :=
    domain.symm ▸ (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  exact congrArg NativeBridge.complexValue
    ((F.call_graphValue _ _ _ g.wd k member).trans (congrFun body k))

theorem matrixDeterminantUpperTriangularFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (g : Obj (M := M) (FormulaFn M))
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (zero : ∀ r, M.mem r (matrixIndexValue n) → ∀ c, M.mem c (matrixIndexValue n) →
      RealLtValue M c r → F.callValue (denote a) (FiniteFunction.pack2 r c) = M.number 0)
    (domain : g.val.signature.domain = finiteSeqDomain n)
    (body : g.val.bodyValue = fun k => F.callValue (denote a) (FiniteFunction.pack2 k k)) :
    matrixDeterminantValue (denote a) n = M.number
      (finiteAggregateValue true (matrixIndexValue n)
        (fun k => NativeBridge.complexValue (F.callValue (denote g) k))) :=
  (matrixDeterminantUpperTriangularValue a n hn ha zero).trans
    (congrArg M.number (finiteDiagonalProductFormula a n g domain body).symm)

theorem matrixDeterminantLowerTriangularFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (g : Obj (M := M) (FormulaFn M))
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (zero : ∀ r, M.mem r (matrixIndexValue n) → ∀ c, M.mem c (matrixIndexValue n) →
      RealLtValue M r c → F.callValue (denote a) (FiniteFunction.pack2 r c) = M.number 0)
    (domain : g.val.signature.domain = finiteSeqDomain n)
    (body : g.val.bodyValue = fun k => F.callValue (denote a) (FiniteFunction.pack2 k k)) :
    matrixDeterminantValue (denote a) n = M.number
      (finiteAggregateValue true (matrixIndexValue n)
        (fun k => NativeBridge.complexValue (F.callValue (denote g) k))) :=
  (matrixDeterminantLowerTriangularValue a n hn ha zero).trans
    (congrArg M.number (finiteDiagonalProductFormula a n g domain body).symm)

end Litex

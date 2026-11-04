import Litex.Multivariable
universe u v w x
namespace Litex

theorem matrixCofactorEntryComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (r c : Fin (NativeBridge.naturalValue (denote n))) :
    NativeBridge.complexValue (matrixCofactorRawValue (denote a) (denote n)
      (FiniteFunction.index r) (FiniteFunction.index c)) =
      (matrixComplexValue (denote a) n n).adjugate c r := by
  have entry := congrFun (congrFun (matrixComplexValueAdjugate a n hn ha) c) r
  change NativeBridge.complexValue (F.callValue (denote (matrixAdjugate a n hn ha))
    (FiniteFunction.pack2 (FiniteFunction.index c) (FiniteFunction.index r))) = _ at entry
  have call := matrixAdjugateCall (matrixAdjugate a n hn ha)
    (FiniteFunction.pack2 (FiniteFunction.index c) (FiniteFunction.index r))
    (matrixDomain_pair n n _ _ (matrixIndexOfFin n hn c) (matrixIndexOfFin n hn r))
  change F.callValue (denote (matrixAdjugate a n hn ha))
    (FiniteFunction.pack2 (FiniteFunction.index c) (FiniteFunction.index r)) =
      matrixAdjugateBody (denote a) n
        (FiniteFunction.pack2 (FiniteFunction.index c) (FiniteFunction.index r)) at call
  unfold matrixAdjugateBody at call
  rw [FiniteFunction.unpack_pack2] at call
  rw [call] at entry
  exact entry

theorem matrixLaplaceTermComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (r c : Fin (NativeBridge.naturalValue (denote n))) :
    NativeBridge.complexValue (M.mulValue
      (F.callValue (denote a) (FiniteFunction.pack2 (FiniteFunction.index r) (FiniteFunction.index c)))
      (matrixCofactorRawValue (denote a) (denote n) (FiniteFunction.index r) (FiniteFunction.index c))) =
      matrixComplexValue (denote a) n n r c * (matrixComplexValue (denote a) n n).adjugate c r := by
  have call := NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha
    (matrixDomain_pair n n _ _ (matrixIndexOfFin n hn r) (matrixIndexOfFin n hn c)))
  have cofactor : matrixCofactorRawValue (denote a) (denote n)
      (FiniteFunction.index r) (FiniteFunction.index c) = M.number
      (NativeBridge.complexValue (matrixCofactorRawValue (denote a) (denote n)
        (FiniteFunction.index r) (FiniteFunction.index c))) := by
    unfold matrixCofactorRawValue
    rw [NativeBridge.complexValue_number]
  rw [call,cofactor,M.mul_numbers,NativeBridge.complexValue_number,
    matrixCofactorEntryComplex a n hn ha r c]
  rfl

theorem matrixDeterminantLaplaceRowValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (row : Obj (M := M) γ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (_hp : In n NPos) (hr : M.mem (denote row) (matrixIndexValue n)) :
    matrixDeterminantValue (denote a) n = M.number
      (finiteAggregateValue false (matrixIndexValue n) (fun k => NativeBridge.complexValue
        (M.mulValue (F.callValue (denote a) (FiniteFunction.pack2 (denote row) k))
          (matrixCofactorRawValue (denote a) (denote n) (denote row) k)))) := by
  obtain ⟨r,hr⟩ := matrixIndexExistsFin n hn (denote row) hr
  change M.number (matrixComplexValue (denote a) n n).det = _
  apply congrArg M.number
  rw [finiteSumMatrixIndex n hn,hr]
  exact (Matrix.det_eq_sum_mul_adjugate_row _ r).trans
    (Finset.sum_congr rfl (fun c _ => (matrixLaplaceTermComplex a n hn ha r c).symm))

theorem matrixDeterminantLaplaceColumnValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (col : Obj (M := M) γ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (_hp : In n NPos) (hc : M.mem (denote col) (matrixIndexValue n)) :
    matrixDeterminantValue (denote a) n = M.number
      (finiteAggregateValue false (matrixIndexValue n) (fun k => NativeBridge.complexValue
        (M.mulValue (F.callValue (denote a) (FiniteFunction.pack2 k (denote col)))
          (matrixCofactorRawValue (denote a) (denote n) k (denote col))))) := by
  obtain ⟨c,hc⟩ := matrixIndexExistsFin n hn (denote col) hc
  change M.number (matrixComplexValue (denote a) n n).det = _
  apply congrArg M.number
  rw [finiteSumMatrixIndex n hn,hc]
  exact (Matrix.det_eq_sum_mul_adjugate_col _ c).trans
    (Finset.sum_congr rfl (fun r _ => (matrixLaplaceTermComplex a n hn ha r c).symm))

theorem finiteLaplaceSumFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α)
    (g : Obj (M := M) (FormulaFn M)) (body : M.Value → M.Value)
    (domain : g.val.signature.domain = finiteSeqDomain n)
    (body_eq : g.val.bodyValue = body) :
    finiteAggregateValue false (matrixIndexValue n)
      (fun k => NativeBridge.complexValue (F.callValue (denote g) k)) =
    finiteAggregateValue false (matrixIndexValue n) (fun k => NativeBridge.complexValue (body k)) := by
  apply finiteAggregateValue_congr
  intro k hk
  have member : M.mem k g.val.signature.domain :=
    domain.symm ▸ (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  exact congrArg NativeBridge.complexValue
    ((F.call_graphValue _ _ _ g.wd k member).trans (congrFun body_eq k))

theorem matrixDeterminantLaplaceRowFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (row : Obj (M := M) γ)
    (g : Obj (M := M) (FormulaFn M)) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hp : In n NPos) (hr : M.mem (denote row) (matrixIndexValue n))
    (domain : g.val.signature.domain = finiteSeqDomain n)
    (body : g.val.bodyValue = fun k => M.mulValue
      (F.callValue (denote a) (FiniteFunction.pack2 (denote row) k))
      (matrixCofactorRawValue (denote a) (denote n) (denote row) k)) :
    matrixDeterminantValue (denote a) n = M.number
      (finiteAggregateValue false (matrixIndexValue n)
        (fun k => NativeBridge.complexValue (F.callValue (denote g) k))) :=
  (matrixDeterminantLaplaceRowValue a n row hn ha hp hr).trans
    (congrArg M.number (finiteLaplaceSumFormula n g _ domain body).symm)

theorem matrixDeterminantLaplaceColumnFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (col : Obj (M := M) γ)
    (g : Obj (M := M) (FormulaFn M)) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hp : In n NPos) (hc : M.mem (denote col) (matrixIndexValue n))
    (domain : g.val.signature.domain = finiteSeqDomain n)
    (body : g.val.bodyValue = fun k => M.mulValue
      (F.callValue (denote a) (FiniteFunction.pack2 k (denote col)))
      (matrixCofactorRawValue (denote a) (denote n) k (denote col))) :
    matrixDeterminantValue (denote a) n = M.number
      (finiteAggregateValue false (matrixIndexValue n)
        (fun k => NativeBridge.complexValue (F.callValue (denote g) k))) :=
  (matrixDeterminantLaplaceColumnValue a n col hn ha hp hc).trans
    (congrArg M.number (finiteLaplaceSumFormula n g _ domain body).symm)

end Litex

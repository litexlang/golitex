import Litex.Multivariable
universe u v1 v2 v3 v4 v5 v6 v7 v8
namespace Litex

theorem nativeRankOfSplitFactorization {m k n : ℕ}
    (U : Matrix (Fin m) (Fin k) ℂ) (V : Matrix (Fin k) (Fin n) ℂ)
    (L : Matrix (Fin k) (Fin m) ℂ) (R : Matrix (Fin n) (Fin k) ℂ)
    (hLU : L * U = 1) (hVR : V * R = 1) : (U * V).rank = k := by
  have identity : (L * (U * V)) * R = 1 := calc
    _ = (L * U) * (V * R) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hLU,hVR,Matrix.one_mul]
  have lower : k ≤ (U * V).rank := calc
    k = (1 : Matrix (Fin k) (Fin k) ℂ).rank := by rw [Matrix.rank_one,Fintype.card_fin]
    _ = ((L * (U * V)) * R).rank := congrArg Matrix.rank identity.symm
    _ ≤ (L * (U * V)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (U * V).rank := Matrix.rank_mul_le_right _ _
  exact Nat.le_antisymm ((Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_width U)) lower

theorem matrixRankFromSplitFactorization {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v1} {β : Type v2} {γ : Type v3} {δ : Type v4}
    {ε : Type v5} {μ : Type v6} {κ : Type v7} {ν : Type v8}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    [Representation M ε] [Representation M μ] [Representation M κ] [Representation M ν]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (left : Obj (M := M) δ) (right : Obj (M := M) ε)
    (m : Obj (M := M) μ) (k : Obj (M := M) κ) (n : Obj (M := M) ν)
    (hm : In m N) (hk : In k N) (hn : In n N)
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hc : M.mem (denote c) (F.fnSetValue (matrixDomain k n) (M.standard .complex)))
    (hl : M.mem (denote left) (F.fnSetValue (matrixDomain k m) (M.standard .complex)))
    (hr : M.mem (denote right) (F.fnSetValue (matrixDomain n k) (M.standard .complex)))
    (ha : Same a (matrixMultiply b c m k n hm hk hn hb hc))
    (hleft : Same (matrixMultiply left b k m k hk hm hk hl hb) (identityMatrix k hk))
    (hright : Same (matrixMultiply c right k n k hk hn hk hc hr) (identityMatrix k hk)) :
    matrixRankValue (denote a) (denote m) (denote n) = denote k := by
  have product := congrArg (fun z => matrixComplexValue z m n) ha
  rw [matrixComplexValueMultiply] at product
  have leftInv := congrArg (fun z => matrixComplexValue z k k) hleft
  rw [matrixComplexValueMultiply,matrixComplexValue_identity] at leftInv
  have rightInv := congrArg (fun z => matrixComplexValue z k k) hright
  rw [matrixComplexValueMultiply,matrixComplexValue_identity] at rightInv
  change M.number ((matrixComplexValue (denote a) m n).rank : ℂ) = denote k
  rw [product,nativeRankOfSplitFactorization _ _ _ _ leftInv rightInv]
  exact (NativeBridge.naturalValue_spec (denote k) hk).symm

end Litex

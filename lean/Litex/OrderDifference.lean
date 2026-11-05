import Litex.OrderedArithmetic

universe u v w
namespace Litex

theorem subNonpositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β))
    (hab : Le p.val.left p.val.right) : Le p (number 0) := by
  obtain ⟨a, b, ha, hb, hab⟩ := hab
  refine NativeBridge.leOfDenoteReal p (number 0) (a - b) 0 ?_ rfl (sub_nonpos.mpr hab)
  change M.subValue (denote p.val.left) (denote p.val.right) = _
  rw [ha, hb, M.sub_numbers, Complex.ofReal_sub]

theorem subNonpositiveToLe {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β))
    (haR : In p.val.left R) (hbR : In p.val.right R)
    (h : Le p (number 0)) : Le p.val.left p.val.right := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp haR
  obtain ⟨b, hb⟩ := (M.real_members _).mp hbR
  have hp : denote p = M.number ((a - b : ℝ) : ℂ) := by
    change M.subValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hb, M.sub_numbers, Complex.ofReal_sub]
  exact NativeBridge.leOfDenoteReal _ _ a b ha hb
    (sub_nonpos.mp ((NativeBridge.le_iff_ofDenoteReal p (number 0) (a - b) 0 hp rfl).mp h))
end Litex

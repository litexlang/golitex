import InteropExamples.ExpectedTarget
import InteropExamples.NumericModel
import Litex.NativeBridge

namespace Adapter

theorem complexAddZero (x : ℂ) : x + 0 = x := by
  let M := Litex.InteropExamples.NumericModel.model
  have h := InteropExamples.ExpectedTarget.addZero
    (M := M) (Litex.number x) (Litex.numberInC x)
  exact (Litex.NativeBridge.addSame_iff (M := M) x 0 x).mp h

theorem realAddZero (x : ℝ) : x + 0 = x := by
  let M := Litex.InteropExamples.NumericModel.model
  have hxR := Litex.NativeBridge.numberInR (M := M) x
  have hxC := InteropExamples.ExpectedTarget.realInComplex (Litex.number (x : ℂ)) hxR
  have h := InteropExamples.ExpectedTarget.addZero (Litex.number (x : ℂ)) hxC
  have hc := (Litex.NativeBridge.addSame_iff (M := M) (x : ℂ) 0 (x : ℂ)).mp h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_add, Complex.ofReal_zero] using hc

end Adapter

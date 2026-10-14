import examples.add_zero.statement

namespace Adapter

theorem complexAddZero (x : ℂ) : x + 0 = x := by
  let M := Litex.NumericModel.model
  have h := LitexCompiled.file_lean_x2f_examples_x2f_add_x5f_zero_x2f_statement_x2e_lit.h_2
    (M := M) (Litex.number x) (Litex.numberInC x)
  exact (Litex.NativeBridge.addSame_iff x 0 x).mp h

end Adapter

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Complex.Basic

namespace RationalMaps

def forward (x : ℚ) : ℚ := (2 * x + 1) / (x - 1)
def backward (y : ℚ) : ℚ := (y + 1) / (y - 2)

end RationalMaps

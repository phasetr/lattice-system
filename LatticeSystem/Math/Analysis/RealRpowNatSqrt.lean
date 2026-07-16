import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# Half-power / square-root bridge for a natural base

A source-independent real-analysis identity: for natural numbers `d, L`, the real power
`(L : ℝ) ^ ((d : ℝ) / 2)` (an `rpow`) equals the ordinary square root `√((L : ℝ) ^ d)` of the
natural power.  This bridges statements phrased with the `rpow` window `L^{d/2}` to the tower
machinery normalized by `√(L^d)`.

It is the shared kernel behind the previously inlined `hbridge` computations of the Anderson tower
(`AndersonTowerTheorem46.lean`, `AndersonTowerTanakaCapstone.lean`) and the Bose–Einstein
condensation tower (Tasaki §5.3, `BoseEinsteinCondensateAlgebra.lean`).
-/

namespace LatticeSystem.Math

/-- **`rpow`–`sqrt` bridge** `L^{d/2} = √(L^d)` for natural `d, L`: the real half-power of the
natural power `L^d` is its square root.  Proved by rewriting `√` as the `1/2`-power and collapsing
`(L^d)^{1/2} = L^{d·(1/2)}`. -/
theorem Ldhalf_bridge (d L : ℕ) :
    (L : ℝ) ^ ((d : ℝ) / 2) = Real.sqrt ((L : ℝ) ^ d) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (L : ℝ) d, ← Real.rpow_mul (Nat.cast_nonneg L)]
  congr 1
  ring

end LatticeSystem.Math

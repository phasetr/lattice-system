/-
Tasaki §4.2.2 Corollary 4.7 (the tower of low-lying energy eigenstates).

Building on Theorem 4.6 (`tower_lowLying_energy_bound`, proved in `AndersonTowerTheorem46`): for each
nonzero magnetization `M` the lowest energy eigenstate in the `Ŝ_tot^{(3)}` sector `μ₀+M` is low-lying.
This file develops the magnetization-sector tools for the torus tower; the first piece is the
magnetization eigenvalue shift of the tower trial state.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerTheorem46

namespace LatticeSystem.Quantum

open Matrix

variable {d L N : ℕ}

/-- **Magnetization shift of an order-density power.**  If `Ŝ_tot^{(3)} v = λ v` then
`Ŝ_tot^{(3)} ((ô^b)^m v) = (λ + m·ε_b) (ô^b)^m v` (`ε_true = +1`, `ε_false = −1`): each order
density `ô^b` shifts the total magnetization by `ε_b`, so `m` of them shift by `m·ε_b`.  This
places the tower trial state `(ô^±)^M Φ` in the magnetization sector `μ₀ ± M`. -/
theorem totalSpinSOp3_mulVec_orderDensityPow_eigenvec [NeZero L] (b : Bool) (m : ℕ)
    {v : (HypercubicTorus d L → Fin (N + 1)) → ℂ} {lam : ℂ}
    (hv : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec v = lam • v) :
    (totalSpinSOp3 (HypercubicTorus d L) N).mulVec
        ((staggeredOrderDensityOpS d L N b ^ m).mulVec v)
      = (lam + (m : ℂ) * (if b then (1 : ℂ) else (-1 : ℂ)))
          • (staggeredOrderDensityOpS d L N b ^ m).mulVec v := by
  induction m with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec,
      totalSpinSOp3_mulVec_orderDensity_eigenvec d L N b ih, Matrix.mulVec_mulVec, ← pow_succ']
    congr 1
    push_cast
    ring

end LatticeSystem.Quantum

import LatticeSystem.Fermion.SpinSBridge

/-!
# Fermion number operator as `1/2 − Ŝ^{(3)}` at spin-`S` (`N = 1`)

The single-mode fermion number operator
`n = !![0, 0; 0, 1]` admits the standard identification

  `n = (1/2) · I − Ŝ^{(3)}`

where `I` is the 2×2 identity and `Ŝ^{(3)}` is the spin-`1/2`
z-component (equivalently spin-`S` at `N = 1`). This identification
follows from `σ^z = 2 Ŝ^{(3)}` and `n = (I − σ^z) / 2`.

Tracked as part of Tasaki §2.1 / §2.4 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `fermionNumber = (1/2) • 1 − spinSOp3 1`: the single-mode
fermion number operator equals `(1/2) − Ŝ^{(3)}` at `N = 1`. -/
theorem fermionNumber_eq_half_smul_one_sub_spinSOp3_one :
    fermionNumber =
      (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        LatticeSystem.Quantum.spinSOp3 1 := by
  unfold fermionNumber LatticeSystem.Quantum.spinSOp3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal] <;> norm_num

end LatticeSystem.Fermion

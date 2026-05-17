import LatticeSystem.Quantum.SpinS.SublatticeSpin
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Spin-`S` sublattice Casimir is positive semi-definite

The sublattice Casimir operator `(Ŝ_A)² := Σ_α (Ŝ_A^(α))²` is positive
semi-definite (PSD) as a sum of squares of Hermitian operators.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-- **`(Ŝ_A^(α))² is PSD`** for Hermitian `Ŝ_A^(α)`. For Hermitian `H`,
`H * H = Hᴴ * H` is PSD. -/
private theorem hermitian_sq_posSemidef
    {H : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    (hH : H.IsHermitian) :
    (H * H).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self H
  rw [hH] at h
  exact h

/-- **`(Ŝ_A)² is PSD`**. -/
theorem sublatticeSpinSquaredS_posSemidef (A : Λ → Bool) :
    (sublatticeSpinSquaredS N A).PosSemidef := by
  rw [sublatticeSpinSquaredS_def]
  exact ((hermitian_sq_posSemidef N (sublatticeSpinSOp1_isHermitian N A)).add
        (hermitian_sq_posSemidef N (sublatticeSpinSOp2_isHermitian N A))).add
      (hermitian_sq_posSemidef N (sublatticeSpinSOp3_isHermitian N A))

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.TotalSquared
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Spin-`S` total Casimir is positive semi-definite

`(Ŝ_tot)² := Σ_α (Ŝ_tot^(α))²` is PSD as a sum of squares of
Hermitian operators. Used in Tasaki §2.5 Theorem 2.3's variational
argument to lower-bound `⟨v|(Ŝ_tot)²|v⟩`.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-- For Hermitian `H`, `H * H` is PSD. -/
private theorem hermitian_sq_posSemidef
    {H : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    (hH : H.IsHermitian) :
    (H * H).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self H
  rw [hH] at h
  exact h

/-- **`(Ŝ_tot)² is PSD`**. Sum of three Hermitian-squares. -/
theorem totalSpinSSquared_posSemidef :
    (totalSpinSSquared Λ N).PosSemidef := by
  rw [totalSpinSSquared_def]
  exact ((hermitian_sq_posSemidef Λ N (totalSpinSOp1_isHermitian Λ N)).add
        (hermitian_sq_posSemidef Λ N (totalSpinSOp2_isHermitian Λ N))).add
      (hermitian_sq_posSemidef Λ N (totalSpinSOp3_isHermitian Λ N))

end LatticeSystem.Quantum

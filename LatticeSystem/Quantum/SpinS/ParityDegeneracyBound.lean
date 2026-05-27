import LatticeSystem.Quantum.SpinS.MagParityEigenspaceDecomp

/-!
# `≤ 2` degeneracy of `Ĥ'` from per-parity-block simplicity

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Combining the eigenspace finrank split under the magnetization-parity involution (#3774) with the
per-parity-block Perron–Frobenius **simplicity** (each parity-block restricted eigenspace has
dimension `≤ 1`), the global `Ĥ'`-eigenspace has dimension `≤ 2`.  This isolates the precise
remaining Perron–Frobenius obligation: the per-block simplicity hypotheses
`finrank (eigenspace Ĥ' μ ⊓ P = ±1) ≤ 1`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **`≤ 2` degeneracy of `Ĥ'`** given per-parity-block simplicity: if each parity-block restricted
`μ`-eigenspace has dimension `≤ 1`, the full `Ĥ'`-eigenspace has dimension `≤ 2`. -/
theorem axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one
    {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ)
    (heven : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D N)) μ ⊓
      End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) 1) ≤ 1)
    (hodd : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D N)) μ ⊓
      End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) (-1)) ≤ 1) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D N)) μ) ≤ 2 := by
  have hsplit := axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_parity_blocks (N := N)
    hJself lam D μ
  omega

end LatticeSystem.Quantum

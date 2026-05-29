import LatticeSystem.Quantum.SpinS.EigenspaceSectorFinrankEq

/-!
# Sector matrix `finrank ≤ 1` transfer to full Hilbert ⊓ sector

(PR #3913, Issue #3739): direct application of PR #3912's finrank equality —
transfer `finrank ≤ 1` from the sector matrix's eigenspace to the full Hilbert
space `⊓` sector subspace.

This completes the within-admissible Perron–Frobenius input transfer needed
for the SU(2) symmetric `finrank ≤ 1` capstone toward Tasaki §2.5 Theorem 2.4
obligation (2.a).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Sector matrix `finrank ≤ 1` ⟹ full Hilbert ⊓ sector `finrank ≤ 1`**: if
the sector matrix's μ-eigenspace has `finrank ≤ 1`, then the full Hilbert space
μ-eigenspace ⊓ the sector subspace also has `finrank ≤ 1`. -/
theorem heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
    (J : Λ → Λ → ℂ) (M : ℕ) (μ : ℂ)
    (h_sector : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N M)) μ) ≤ 1) :
    finrank ℂ ↥((End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ⊓
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) ≤ 1 := by
  rw [← heisenbergHamiltonianS_sector_matrix_eigenspace_finrank_eq]
  exact h_sector

end LatticeSystem.Quantum

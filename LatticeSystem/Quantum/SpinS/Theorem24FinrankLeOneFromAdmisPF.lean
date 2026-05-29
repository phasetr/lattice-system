import LatticeSystem.Quantum.SpinS.Theorem24EigvecInAdmisSector

/-!
# `finrank ≤ 1` from admissible-sector PF + `finrank ≤ 2`

(PR #3906, Issue #3739): combines PR #3905 (eigvec ⊆ admissible sector) with
within-admissible-sector PF `finrank ≤ 1` to get full Hilbert space
`finrank ≤ 1`.

Abstract finrank-counting step toward the SU(2) symmetric `finrank ≤ 1`
capstone, conditional on the within-admissible PF input.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **`finrank ≤ 1` from admissible-sector PF + `finrank ≤ 2`**: if the
anisotropic Hamiltonian eigenspace at `μ` has `finrank ≤ 2` AND an admissible
eigvec exists at `μ` AND the within-admissible-sector eigenspace at `μ` has
`finrank ≤ 1`, then the full Hilbert space eigenspace at `μ` has `finrank ≤ 1`. -/
theorem anisotropicHeisenbergS_finrank_le_one_from_admis_pf
    (J : Λ → Λ → ℂ) (lam D μ : ℂ)
    (h_finrank_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_admis : Φ ∈ magSubspaceS Λ N 0) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (anisotropicHeisenbergS J lam D N).mulVec Φ = μ • Φ)
    (h_admis_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ ⊓ magSubspaceS Λ N 0) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 1 := by
  classical
  set E := End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ with hEdef
  set A := magSubspaceS Λ N 0 with hAdef
  -- E ⊆ A by PR #3905, so E ⊓ A = E.
  have h_subset : E ≤ A := by
    intro Ψ hΨ_mem
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply] at hΨ_mem
    rw [hAdef]
    exact anisotropicHeisenbergS_eigvec_in_admis_sector_of_finrank_le_two
      J lam D μ h_finrank_le_two hΦ_admis hΦ_ne hΦ_eig hΨ_mem
  have h_inter_eq : E ⊓ A = E := inf_eq_left.mpr h_subset
  rw [h_inter_eq] at h_admis_pf
  exact h_admis_pf

end LatticeSystem.Quantum

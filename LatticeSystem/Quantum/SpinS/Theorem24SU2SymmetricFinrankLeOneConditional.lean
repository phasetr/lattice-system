import LatticeSystem.Quantum.SpinS.Theorem24FinrankLeOneFromAdmisPF
import LatticeSystem.Quantum.SpinS.Theorem24SU2BaseCase

/-!
# SU(2) symmetric `finrank ≤ 1` (conditional on within-admissible PF)

(PR #3907, Issue #3739): packaging of PR #3906 at the SU(2) point `(λ=1, D=0)`
via the reduction `anisotropicHeisenbergS_one_zero` (PR #3897 bridge). Gives the
isotropic Heisenberg `finrank ≤ 1` at `μ` conditional on:
- obligation (1) `finrank ≤ 2` (e.g., from PR #3888 for spin-1/2).
- admissible eigvec `Φ ≠ 0` at `μ`.
- within-admissible PF input: `finrank (eigenspace ⊓ admissible) ≤ 1`.

The SU(2) endpoint of the deformation argument toward Theorem 2.4 obligation
(2.a): the deformation can now propagate from this μ point.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **SU(2) symmetric `finrank ≤ 1` (conditional)**: at the SU(2) point
`(λ=1, D=0)` the anisotropic Hamiltonian equals the isotropic Heisenberg
(PR #3897); given `finrank ≤ 2` + admis. eigvec exists + within-admis PF input,
the isotropic Heisenberg eigenspace at `μ` has `finrank ≤ 1`. -/
theorem heisenbergHamiltonianS_finrank_le_one_at_SU2_conditional
    (J : Λ → Λ → ℂ) (μ : ℂ)
    (h_finrank_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_admis : Φ ∈ magSubspaceS Λ N 0) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = μ • Φ)
    (h_admis_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := Λ) J N)) μ ⊓ magSubspaceS Λ N 0) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ≤ 1 := by
  -- Transport through `anisotropicHeisenbergS_at_SU2_eigenspace_eq` (PR #3897).
  have h_eigsp_eq := anisotropicHeisenbergS_at_SU2_eigenspace_eq_heisenbergHamiltonianS
    (Λ := Λ) (N := N) J μ
  -- Anisotropic at (1, 0) finrank ≤ 2.
  have h_aniso_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 0 N)) μ) ≤ 2 := by
    rw [h_eigsp_eq]; exact h_finrank_le_two
  -- Anisotropic at (1, 0) admis. eigvec.
  have h_aniso_eig : (anisotropicHeisenbergS J 1 0 N).mulVec Φ = μ • Φ := by
    rw [anisotropicHeisenbergS_one_zero]
    exact hΦ_eig
  -- Anisotropic at (1, 0) within-admis PF.
  have h_aniso_admis_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 0 N)) μ ⊓ magSubspaceS Λ N 0) ≤ 1 := by
    rw [h_eigsp_eq]; exact h_admis_pf
  -- Apply PR #3906.
  have h_aniso_le_one : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 0 N)) μ) ≤ 1 :=
    anisotropicHeisenbergS_finrank_le_one_from_admis_pf
      J 1 0 μ h_aniso_le_two hΦ_admis hΦ_ne h_aniso_eig h_aniso_admis_pf
  rw [h_eigsp_eq] at h_aniso_le_one
  exact h_aniso_le_one

end LatticeSystem.Quantum

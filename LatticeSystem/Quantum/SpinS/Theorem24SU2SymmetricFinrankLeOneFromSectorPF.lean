import LatticeSystem.Quantum.SpinS.Theorem24SU2SymmetricFinrankLeOneConditional
import LatticeSystem.Quantum.SpinS.EigenspaceFinrankLeOneTransfer

/-!
# SU(2) symmetric `finrank ≤ 1` from sector matrix PF

(PR #3915, Issue #3739): combines PR #3907 (SU(2) symmetric `finrank ≤ 1`
conditional on within-admissible PF) and PR #3913 (sector matrix `finrank ≤ 1`
transfer to full Hilbert ⊓ sector) to express the SU(2) symmetric `finrank ≤ 1`
conclusion with the within-admissible PF input at the **sector matrix** level
— matching the output form of the existing Theorem 2.3 chain's PF analysis.

Conditional on:
- obligation (1) `finrank ≤ 2` (e.g., from PR #3888 for spin-1/2).
- admissible eigvec `Φ ≠ 0` at μ.
- sector index `M` with `2M = |Λ|·N` (the symmetric `|A|=|¬A|` admissible
  sector value).
- within-admissible sector-matrix PF: `finrank ≤ 1` for the sector matrix's
  μ-eigenspace.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **SU(2) symmetric `finrank ≤ 1` from sector matrix PF**: combines PR #3907
and PR #3913 to give the SU(2) symmetric `finrank ≤ 1` conclusion with the
within-admissible PF input at the sector matrix level. -/
theorem heisenbergHamiltonianS_finrank_le_one_at_SU2_from_sector_pf
    (J : Λ → Λ → ℂ) (μ : ℂ)
    (h_finrank_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_admis : Φ ∈ magSubspaceS Λ N 0) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = μ • Φ)
    (M : ℕ) (hM_admis : 2 * M = Fintype.card Λ * N)
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N M)) μ) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ≤ 1 := by
  -- Apply PR #3913: sector PF ⟹ full ⊓ sector finrank ≤ 1.
  have h_admis_pf := heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
    (Λ := Λ) (N := N) J M μ h_sector_pf
  -- The sector subspace eigenvalue (|Λ|·N/2 - M : ℂ) = 0 since 2M = |Λ|·N.
  have h_M_eq : ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ) = 0 := by
    have h_cast : ((2 * M : ℕ) : ℂ) = ((Fintype.card Λ * N : ℕ) : ℂ) :=
      congrArg ((↑) : ℕ → ℂ) hM_admis
    push_cast at h_cast
    linear_combination -h_cast / 2
  rw [h_M_eq] at h_admis_pf
  -- Apply PR #3907.
  exact heisenbergHamiltonianS_finrank_le_one_at_SU2_conditional
    J μ h_finrank_le_two hΦ_admis hΦ_ne hΦ_eig h_admis_pf

end LatticeSystem.Quantum

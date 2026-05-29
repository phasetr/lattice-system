import LatticeSystem.Quantum.SpinS.MagSubspaceDistinctTripleLI
import LatticeSystem.Quantum.SpinS.AnisotropicReflectionEigenspace

/-!
# Three-LI family from admissible + non-admissible eigenvectors (SU(2) symmetric case)

(PR #3902, Issue #3739): if the anisotropic Hamiltonian has both an
admissible-sector eigenvector `Φ` (at `Ŝ³_tot = 0`) and a non-admissible-sector
eigenvector `Ψ` (at `Ŝ³_tot = M' ≠ 0`) at the same energy `μ`, then
`{Φ, Ψ, Θ Ψ}` is a linearly independent family in the eigenspace.

This is the contradiction lever for the SU(2) symmetric `finrank ≤ 1` argument:
combined with obligation (1)'s `finrank ≤ 2`, it forces no non-admissible-sector
eigenstate to exist at the GS energy.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Three-LI from admissible + non-admissible vectors via reflection**: a non-zero
admissible-sector vector Φ (at `Ŝ³_tot = 0`) and a non-zero non-admissible-sector
vector Ψ (at `Ŝ³_tot = M' ≠ 0`), together with the reflected vector
`Θ Ψ ∈ magSubspaceS Λ N (-M')`, form a linearly independent family.

Sector-membership-only — the lemma does not require Φ, Ψ to be H-eigenvectors,
though the intended use case is: Φ, Ψ both H-eigenvectors at the same energy μ,
in which case `Θ Ψ` is also at energy μ (since `Θ` commutes with H via #3745),
making the family a 3-LI subset of the μ-eigenspace and giving the contradiction
lever `finrank(eigenspace at μ) ≥ 3` against obligation (1) `finrank ≤ 2`. -/
theorem anisotropicHeisenbergS_threeLI_of_admis_and_nonadmis
    {Φ Ψ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_admis : Φ ∈ magSubspaceS Λ N 0) (hΦ_ne : Φ ≠ 0)
    {M' : ℂ} (hM'_ne : M' ≠ 0)
    (hΨ_nonadmis : Ψ ∈ magSubspaceS Λ N M') (hΨ_ne : Ψ ≠ 0) :
    LinearIndependent ℂ
      ![Φ, Ψ, (manyBodyReversalS Λ N).mulVec Ψ] := by
  classical
  set ΘΨ := (manyBodyReversalS Λ N).mulVec Ψ with hΘΨdef
  -- ΘΨ ∈ magSubspaceS Λ N (-M') via reflection sector shift.
  have hΘΨ_mem : ΘΨ ∈ magSubspaceS Λ N (-M') :=
    manyBodyReversalS_mulVec_mem_magSubspaceS_neg hΨ_nonadmis
  -- ΘΨ ≠ 0: since Θ² = 1, Θ is invertible, hence ΘΨ = 0 ⟹ Ψ = 0.
  have hΘΨ_ne : ΘΨ ≠ 0 := by
    intro h0
    apply hΨ_ne
    have h_inv : (manyBodyReversalS Λ N).mulVec ΘΨ = Ψ := by
      rw [hΘΨdef, Matrix.mulVec_mulVec, manyBodyReversalS_mul_self, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h_inv
    exact h_inv.symm
  -- Three sectors 0, M', -M' are pairwise distinct.
  have h0_M' : (0 : ℂ) ≠ M' := Ne.symm hM'_ne
  have h0_negM' : (0 : ℂ) ≠ -M' := by
    intro heq
    apply hM'_ne
    exact neg_eq_zero.mp heq.symm
  have hM'_negM' : M' ≠ -M' := by
    intro heq
    apply hM'_ne
    -- M' = -M' ⟹ M' + M' = 0 ⟹ M' = 0
    have hsum : M' + M' = 0 := by
      nth_rewrite 1 [heq]
      exact neg_add_cancel M'
    have h2M' : (2 : ℂ) * M' = 0 := by
      rw [show (2 : ℂ) * M' = M' + M' by ring]
      exact hsum
    have h2_ne : (2 : ℂ) ≠ 0 := two_ne_zero
    rcases mul_eq_zero.mp h2M' with h | h
    · exact absurd h h2_ne
    · exact h
  -- Apply triple-LI.
  exact linearIndependent_triple_of_magSubspaceS_distinct
    h0_M' h0_negM' hM'_negM'
    hΦ_admis hΦ_ne hΨ_nonadmis hΨ_ne hΘΨ_mem hΘΨ_ne

end LatticeSystem.Quantum

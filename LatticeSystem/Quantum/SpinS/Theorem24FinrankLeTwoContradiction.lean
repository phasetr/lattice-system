import LatticeSystem.Quantum.SpinS.Theorem24ThreeLIFromNonAdmis
import LatticeSystem.Quantum.SpinS.AnisotropicReflectionSymmetry

/-!
# Contradiction: `finrank ≤ 2` + admissible eigenvec + non-admissible eigenvec → False

(PR #3903, Issue #3739): if the anisotropic Hamiltonian has `finrank ≤ 2` at
energy `μ` AND an admissible-sector eigenvector AND a non-admissible-sector
eigenvector at the same `μ`, then `False`. Combines PR #3902's three-LI with
the fact that `Θ` (the spin reversal) commutes with `H` (#3745), so `Θ Ψ` is
also at energy `μ` and the three-LI family lives in the eigenspace, giving
`finrank ≥ 3` contradicting `≤ 2`.

This is the direct contradiction in the SU(2) symmetric `finrank ≤ 1` argument
toward Tasaki §2.5 Theorem 2.4 obligation (2.a).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **`finrank ≤ 2` + admissible eigenvec + non-admissible eigenvec → False**: at
energy `μ` of the anisotropic Hamiltonian, if the eigenspace has `finrank ≤ 2`
and contains both an admissible-sector eigenvector Φ (at `Ŝ³_tot = 0`) and a
non-admissible-sector eigenvector Ψ (at `Ŝ³_tot = M' ≠ 0`), then `False`. -/
theorem anisotropicHeisenbergS_finrank_le_two_no_admis_plus_nonadmis
    (J : Λ → Λ → ℂ) (lam D μ : ℂ)
    (h_finrank : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_admis : Φ ∈ magSubspaceS Λ N 0) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (anisotropicHeisenbergS J lam D N).mulVec Φ = μ • Φ)
    {Ψ : (Λ → Fin (N + 1)) → ℂ}
    {M' : ℂ} (hM'_ne : M' ≠ 0)
    (hΨ_nonadmis : Ψ ∈ magSubspaceS Λ N M') (hΨ_ne : Ψ ≠ 0)
    (hΨ_eig : (anisotropicHeisenbergS J lam D N).mulVec Ψ = μ • Ψ) : False := by
  classical
  set H := anisotropicHeisenbergS (Λ := Λ) J lam D N with hHdef
  set E := End.eigenspace (Matrix.toLin' H) μ with hEdef
  set ΘΨ := (manyBodyReversalS Λ N).mulVec Ψ with hΘΨdef
  -- {Φ, Ψ, ΘΨ} is linearly independent via PR #3902.
  have hLI : LinearIndependent ℂ ![Φ, Ψ, ΘΨ] :=
    anisotropicHeisenbergS_threeLI_of_admis_and_nonadmis
      hΦ_admis hΦ_ne hM'_ne hΨ_nonadmis hΨ_ne
  -- Each of Φ, Ψ, ΘΨ is in eigenspace E at μ.
  have hΦ_mem_E : Φ ∈ E := by
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hΦ_eig
  have hΨ_mem_E : Ψ ∈ E := by
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hΨ_eig
  have hΘΨ_mem_E : ΘΨ ∈ E := by
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply, hHdef]
    rw [hΘΨdef, Matrix.mulVec_mulVec, anisotropicHeisenbergS_mul_manyBodyReversalS,
        ← Matrix.mulVec_mulVec, hΨ_eig, Matrix.mulVec_smul]
  -- Build a 3-LI family in the subspace E.
  let v : Fin 3 → ↥E := ![⟨Φ, hΦ_mem_E⟩, ⟨Ψ, hΨ_mem_E⟩, ⟨ΘΨ, hΘΨ_mem_E⟩]
  have hLI_E : LinearIndependent ℂ v := by
    have hcomp : (E.subtype : ↥E →ₗ[ℂ] (Λ → Fin (N + 1)) → ℂ) ∘ v = ![Φ, Ψ, ΘΨ] := by
      funext i
      fin_cases i <;> rfl
    have := hLI
    rw [← hcomp] at this
    exact LinearIndependent.of_comp E.subtype this
  -- 3 ≤ finrank E from 3-LI.
  have h3_le : 3 ≤ finrank ℂ ↥E := by
    have := hLI_E.fintype_card_le_finrank
    simpa using this
  -- Contradiction with finrank ≤ 2.
  omega

end LatticeSystem.Quantum

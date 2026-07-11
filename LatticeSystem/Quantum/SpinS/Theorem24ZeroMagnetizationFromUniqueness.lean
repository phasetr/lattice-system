import LatticeSystem.Quantum.SpinS.AnisotropicReflectionEigenspace
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergU1
import LatticeSystem.Math.MatrixAnalysis.UniqueEigenspaceInvolution
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Tasaki §2.5 Theorem 2.4 partial: unique GS has zero `Ŝ³_tot` magnetization

(PR #3896, Issue #3739): if the anisotropic Heisenberg Hamiltonian's ground-state
eigenspace has `finrank ≤ 1` (uniqueness), then the ground state `Φ` satisfies
`Ŝ³_tot Φ = 0`. This is part of Tasaki Theorem 2.4's full conclusion (the other
part is uniqueness itself, established by the deformation argument from the SU(2)
point — separate work).

Proof sketch:
1. The eigenspace `E` is invariant under both `Ŝ³_tot` (since `[H, Ŝ³_tot] = 0`)
   and the reflection `Θ` (since `[H, Θ] = 0`).
2. From `finrank E ≤ 1` and `Φ ≠ 0`, every element of `E` is a scalar multiple
   of `Φ`. Hence `Ŝ³_tot Φ = γ Φ` and `Θ Φ = δ Φ` for some `γ, δ ∈ ℂ`.
3. `Θ² = 1` ⟹ `δ² = 1` ⟹ `δ ≠ 0`.
4. `Θ Ŝ³_tot = -Ŝ³_tot Θ` ⟹ apply to `Φ`:
   `Θ (γΦ) = γΘΦ = γδΦ` and `-Ŝ³_tot (Θ Φ) = -Ŝ³_tot (δΦ) = -δγΦ`,
   so `γδ = -δγ`, hence `2δγ = 0`, hence `γ = 0` (since `δ ≠ 0`).
5. `Ŝ³_tot Φ = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Tasaki §2.5 Theorem 2.4 partial conclusion (`Ŝ³_tot|Φ⟩ = 0` from uniqueness)**:
if the anisotropic Heisenberg ground-state eigenspace has `finrank ≤ 1`, then any
non-zero ground state has zero total `Ŝ³` magnetization. -/
theorem anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (J : Λ → Λ → ℂ) (lam D μ : ℂ)
    (huniq : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 1)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ : (anisotropicHeisenbergS J lam D N).mulVec Φ = μ • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  set H := anisotropicHeisenbergS (Λ := Λ) J lam D N with hHdef
  set E := End.eigenspace (Matrix.toLin' H) μ with hEdef
  -- Φ ∈ E.
  have hΦ_in : Φ ∈ E := by
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hΦ
  -- Ŝ³_tot Φ ∈ E (via [H, Ŝ³_tot] = 0).
  have hSΦ_in : (totalSpinSOp3 Λ N).mulVec Φ ∈ E := by
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply, hHdef]
    rw [Matrix.mulVec_mulVec,
        (anisotropicHeisenbergS_commute_totalSpinSOp3 J lam D N).eq,
        ← Matrix.mulVec_mulVec, hΦ, Matrix.mulVec_smul]
  -- The reflection `Θ` acts as `δ` (`= ±1`) on the unique ground state (shared eigenspace lemma).
  obtain ⟨δ, hΘΦ_eq, hδ2_eq⟩ :=
    LatticeSystem.Math.exists_involution_eigenvalue_of_unique_eigenspace H
      (manyBodyReversalS Λ N) μ huniq hΦ_ne hΦ
      (anisotropicHeisenbergS_mul_manyBodyReversalS J lam D) (manyBodyReversalS_mul_self Λ N)
  -- `Ŝ³_tot Φ` is a scalar multiple `γ • Φ` (same eigenspace, uniqueness).
  obtain ⟨γ, hSΦ_eq⟩ :=
    LatticeSystem.Math.exists_smul_of_mem_finrank_le_one huniq hΦ_in hΦ_ne hSΦ_in
  -- `δ ≠ 0` from `δ² = 1`.
  have hδ_ne : δ ≠ 0 := by
    intro h0
    rw [h0, pow_two, mul_zero] at hδ2_eq
    exact zero_ne_one hδ2_eq
  -- Anticommutation: Ŝ³_tot Θ Φ = - Θ Ŝ³_tot Φ.
  -- LHS: Ŝ³_tot (Θ Φ) = Ŝ³_tot (δ Φ) = δ (Ŝ³_tot Φ) = δγ Φ.
  -- RHS: -Θ (Ŝ³_tot Φ) = -Θ (γΦ) = -γ (Θ Φ) = -γδ Φ.
  -- So δγ = -γδ ⟹ 2δγ = 0 ⟹ δγ = 0 ⟹ γ = 0.
  have hanti : (totalSpinSOp3 Λ N).mulVec ((manyBodyReversalS Λ N).mulVec Φ) =
      -(manyBodyReversalS Λ N).mulVec ((totalSpinSOp3 Λ N).mulVec Φ) := by
    rw [Matrix.mulVec_mulVec, totalSpinSOp3_mul_manyBodyReversalS,
        Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  have hLHS : (totalSpinSOp3 Λ N).mulVec ((manyBodyReversalS Λ N).mulVec Φ) =
      (δ * γ) • Φ := by
    rw [hΘΦ_eq, Matrix.mulVec_smul, hSΦ_eq, smul_smul]
  have hRHS : -(manyBodyReversalS Λ N).mulVec ((totalSpinSOp3 Λ N).mulVec Φ) =
      -(γ * δ) • Φ := by
    rw [hSΦ_eq, Matrix.mulVec_smul, hΘΦ_eq, smul_smul, neg_smul]
  have hδγ_eq : (δ * γ) • Φ = -(γ * δ) • Φ := hLHS.symm.trans (hanti.trans hRHS)
  -- 2δγ = 0 from δγ = -δγ.
  have h_double : (δ * γ) • Φ + (δ * γ) • Φ = 0 := by
    nth_rewrite 1 [hδγ_eq]
    rw [neg_smul, mul_comm γ δ]
    exact neg_add_cancel ((δ * γ) • Φ)
  have h2δγ : (2 * (δ * γ)) • Φ = 0 := by
    rw [show (2 : ℂ) * (δ * γ) = (δ * γ) + (δ * γ) by ring, add_smul]
    exact h_double
  have hδγ : δ * γ = 0 := by
    have h2_ne : (2 : ℂ) ≠ 0 := two_ne_zero
    have := (smul_eq_zero.mp h2δγ).resolve_right hΦ_ne
    exact (mul_eq_zero.mp this).resolve_left h2_ne
  have hγ : γ = 0 := by
    rcases mul_eq_zero.mp hδγ with h | h
    · exact absurd h hδ_ne
    · exact h
  -- Conclude.
  rw [hSΦ_eq, hγ, zero_smul]

end LatticeSystem.Quantum

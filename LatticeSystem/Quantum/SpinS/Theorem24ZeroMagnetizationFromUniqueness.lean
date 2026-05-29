import LatticeSystem.Quantum.SpinS.AnisotropicReflectionEigenspace
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergU1
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
  -- Θ Φ ∈ E (via H Θ = Θ H).
  have hΘΦ_in : (manyBodyReversalS Λ N).mulVec Φ ∈ E := by
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply, hHdef]
    rw [Matrix.mulVec_mulVec,
        anisotropicHeisenbergS_mul_manyBodyReversalS,
        ← Matrix.mulVec_mulVec, hΦ, Matrix.mulVec_smul]
  -- From finrank ≤ 1, extract a generator v of E.
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp huniq
  -- Φ = a • v.val, Ŝ³_tot Φ = b • v.val, Θ Φ = c • v.val.
  obtain ⟨a, ha⟩ := hv ⟨Φ, hΦ_in⟩
  obtain ⟨b, hb⟩ := hv ⟨_, hSΦ_in⟩
  obtain ⟨c, hc⟩ := hv ⟨_, hΘΦ_in⟩
  -- Underlying vector equations.
  have ha' : a • (v : (Λ → Fin (N + 1)) → ℂ) = Φ := by
    have h := congrArg ((↑) : ↥E → (Λ → Fin (N + 1)) → ℂ) ha
    simpa using h
  have hb' : b • (v : (Λ → Fin (N + 1)) → ℂ) = (totalSpinSOp3 Λ N).mulVec Φ := by
    have h := congrArg ((↑) : ↥E → (Λ → Fin (N + 1)) → ℂ) hb
    simpa using h
  have hc' : c • (v : (Λ → Fin (N + 1)) → ℂ) = (manyBodyReversalS Λ N).mulVec Φ := by
    have h := congrArg ((↑) : ↥E → (Λ → Fin (N + 1)) → ℂ) hc
    simpa using h
  -- a ≠ 0 (since Φ ≠ 0).
  have ha_ne : a ≠ 0 := by
    intro h0
    apply hΦ_ne
    rw [← ha', h0, zero_smul]
  -- Derive Ŝ³_tot Φ = (b/a) • Φ and Θ Φ = (c/a) • Φ.
  have hSΦ_eq : (totalSpinSOp3 Λ N).mulVec Φ = (b * a⁻¹) • Φ := by
    rw [← hb', ← ha', smul_smul, mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]
  have hΘΦ_eq : (manyBodyReversalS Λ N).mulVec Φ = (c * a⁻¹) • Φ := by
    rw [← hc', ← ha', smul_smul, mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]
  set γ := b * a⁻¹ with hγdef
  set δ := c * a⁻¹ with hδdef
  -- Θ²Φ = Φ ⟹ δ² Φ = Φ ⟹ δ² = 1 (since Φ ≠ 0) ⟹ δ ≠ 0.
  have hΘ2 : (manyBodyReversalS Λ N).mulVec ((manyBodyReversalS Λ N).mulVec Φ) = Φ := by
    rw [Matrix.mulVec_mulVec, manyBodyReversalS_mul_self, Matrix.one_mulVec]
  have hδ2 : δ ^ 2 • Φ = Φ := by
    have h := hΘ2
    rw [hΘΦ_eq, Matrix.mulVec_smul, hΘΦ_eq, smul_smul, ← sq] at h
    exact h
  have hδ2_eq : δ ^ 2 = 1 := by
    have hΦne_smul : (1 : ℂ) • Φ = Φ := one_smul _ _
    have heq : δ ^ 2 • Φ = (1 : ℂ) • Φ := hδ2.trans hΦne_smul.symm
    by_contra hne
    have hsub : (δ ^ 2 - 1) • Φ = 0 := by
      rw [sub_smul, heq, sub_self]
    have hdiff_ne : δ ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hne
    exact hΦ_ne ((smul_eq_zero.mp hsub).resolve_left hdiff_ne)
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

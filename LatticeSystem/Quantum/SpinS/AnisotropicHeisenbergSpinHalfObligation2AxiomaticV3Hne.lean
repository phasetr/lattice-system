import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfObligation2AxiomaticV3
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergCrossingDualSectorGroundExplicit

/-!
# Spin-1/2 Tasaki §2.5 Theorem 2.4 obligation (2) — capstone v3' (hne hypothesis)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Variant of PR #4001's capstone v3 that takes the non-emptiness hypothesis
`hne : (perMCrossingSet M ∩ Icc 0 1).Nonempty` directly, rather than
deriving it from `h_violation` at `γ(1)`. This enables composition with
the argmin extraction (PR #4007), where the argmin's `M_chosen` has a
non-empty crossing set but not necessarily at `γ(1)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 obligation (2) capstone v3' (hne hypothesis)**: identical proof
to PR #4001's capstone v3, but takes `hne` directly instead of deriving it
from `h_violation` at `γ(1)`. Enables composition with argmin extraction. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing_hne
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_ne_balanced :
      (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    -- hne: non-emptiness of the crossing set ∩ Icc 0 1 for THIS M.
    (hne :
      (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1).Nonempty)
    (h_strict_gap_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M lam' D' 0)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1
          (anisotropicHeisenbergParametricPath lam' D' 0).1
          (anisotropicHeisenbergParametricPath lam' D' 0).2))
    (h_balanced_GS_below : ∀ t' : ℝ, t' ∈ Ico (0 : ℝ)
        (sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)) →
      t' ∈ balancedGSSet (Λ := Λ) hJ_star 1 M_balanced lam' D') :
    False := by
  classical
  set t := sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)
    with ht_def
  have hmem : t ∈ perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1 :=
    sInf_perMCrossingSet_inter_Icc_mem hJ_star 1 M_balanced M lam' D' hne
  have ht_nn : 0 ≤ t := hmem.2.1
  have ht_le : t ≤ 1 := hmem.2.2
  have ht_pos : 0 < t := by
    rcases lt_or_eq_of_le ht_nn with hpos | h0_eq
    · exact hpos
    · exfalso
      have h_in := hmem.1
      simp only [perMCrossingSet, Set.mem_setOf_eq] at h_in
      rw [← h0_eq] at h_in
      linarith
  have h_eq_at_t := anisotropicHeisenbergS_per_M_crossing_equality_at_sInf
    hJ_star 1 M_balanced M lam' D' hne h_strict_gap_SU2
  have h_bal_eq_full_def := balanced_min_eq_full_at_sInf
    hJ_star 1 M_balanced M lam' D' hne h_GS_at_SU2 h_balanced_GS_below
  have h_bal_eq_full : hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) := h_bal_eq_full_def
  obtain ⟨Φ_bal, hΦ_bal_ne, hΦ_bal_eig, hΦ_bal_mem⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 1 M_balanced
  obtain ⟨Φ_M, hΦ_M_ne, hΦ_M_eig, hΦ_M_mem⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 1 M
  have h_eq_at_t' : hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := 1) (M := M) hJ_star
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2) =
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := 1) (M := M_balanced) hJ_star
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2) := h_eq_at_t
  rw [h_eq_at_t'] at hΦ_M_eig
  rw [h_bal_eq_full] at hΦ_bal_eig
  have h_finrank :=
    spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_path
      A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
      hlam'_lb hlam'_ub hD' ht_pos ht_le
  rw [h_bal_eq_full] at hΦ_M_eig
  exact anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two
    J ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
      ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) _
    h_finrank hΦ_bal_ne h_balanced hΦ_bal_eig
    hΦ_M_ne hM_ne_balanced hΦ_M_eig

end LatticeSystem.Quantum

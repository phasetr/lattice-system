import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfObligation2AxiomaticV3Hne
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergArgminExtraction
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedBelowFromArgmin
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGapAllMFromArgmin

/-!
# Spin-1/2 Tasaki §2.5 Theorem 2.4 obligation (2) — capstone v5 (FINAL composed)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

★★★ Final composed capstone: discharges PR #4001's "below-sInf balanced IS
GS" via the argmin extraction (PR #4007) + the below-from-argmin (PR #4002) +
strict-gap-all-M (PR #4003), and applies capstone v3' hne (PR #4009) on the
extracted argmin's `M_chosen`.

**Two explicit axioms remain**:
1. **(2-IVT-c) strict gap at `(1, 0)`** path-wide for all `M ≠ M_balanced` (non-empty).
2. **Strict-GS at `(1, 0)`** — discharges via PR #3990 once strict gap at `(1, 0)` for
   ALL `M' ≠ M_balanced` is in scope (here the same axiom).

Equivalent to "spin-1/2 Tasaki §2.5 Theorem 2.4 obligation (2) holds modulo
the strict-gap axiom at the SU(2) point `(1, 0)`".

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **★★★ Spin-1/2 obligation (2) capstone v5 (FINAL composed)**: derives False
under any specific violation `M_orig` + strict gap at `(1, 0)` for ALL valid
sectors + strict-GS at `(1, 0)`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_final
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
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    -- For every M' ≠ M_balanced (in range), centered magnetization is non-zero.
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1)
    -- ★ Axiom 1: strict gap at (1, 0) for all valid M' ≠ M_balanced.
    (axiom_strict_gap_at_SU2 :
      ∀ M' : ℕ, [Nonempty (magConfigS Λ 1 M')] → M' ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M' lam' D' 0)
    -- ★ Axiom 2: strict-GS at (1, 0).
    (axiom_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1
          (anisotropicHeisenbergParametricPath lam' D' 0).1
          (anisotropicHeisenbergParametricPath lam' D' 0).2)) :
    False := by
  classical
  -- M_orig has non-empty crossing set.
  have hne_orig : (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M_orig lam' D' ∩
      Icc (0 : ℝ) 1).Nonempty :=
    ⟨1, h_violation_orig, ⟨by norm_num, le_refl _⟩⟩
  -- Extract argmin M_chosen.
  obtain ⟨M_chosen, hM_chosen_range, hM_chosen_ne_bal, hM_chosen_NE,
          hM_chosen_cross_total, h_argmin_total⟩ :=
    exists_M_chosen_argmin_per_M_first_crossing
      hJ_star 1 M_balanced M_orig hM_orig_ne lam' D' hne_orig
  haveI := hM_chosen_NE
  -- Convert total ↔ partial.
  have hM_chosen_cross :
      (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M_chosen lam' D' ∩
        Icc (0 : ℝ) 1).Nonempty := by
    rw [← perMCrossingSet_total_eq_perMCrossingSet]
    exact hM_chosen_cross_total
  -- Centered non-zero for M_chosen.
  have hM_chosen_centered_ne : (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) -
      (M_chosen : ℂ)) ≠ 0 :=
    h_centered_nonzero M_chosen hM_chosen_range hM_chosen_ne_bal
  -- Strict gap at (1, 0) for M_chosen.
  have h_strict_chosen :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_chosen lam' D' 0 :=
    axiom_strict_gap_at_SU2 M_chosen hM_chosen_ne_bal
  -- Build the argmin hypothesis in partial form.
  have h_argmin : ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ 1 M'), M' ≠ M_balanced →
      (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1).Nonempty →
      sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M_chosen lam' D' ∩
        Icc (0 : ℝ) 1) ≤
      sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩
        Icc (0 : ℝ) 1) := by
    intro M' hNE_M' h_ne_bal_M' h_cross_M'
    haveI := hNE_M'
    have hM'_range : M' ∈ Finset.range (Fintype.card Λ * 1 + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hNE_M'
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    have h_cross_M'_total :
        (perMCrossingSet_total (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩
          Icc (0 : ℝ) 1).Nonempty := by
      rw [perMCrossingSet_total_eq_perMCrossingSet]
      exact h_cross_M'
    have h_le_total := h_argmin_total M' hM'_range h_ne_bal_M' hNE_M' h_cross_M'_total
    rw [perMCrossingSet_total_eq_perMCrossingSet,
        perMCrossingSet_total_eq_perMCrossingSet] at h_le_total
    exact h_le_total
  -- Derive the "below sInf balanced IS GS" hypothesis.
  have h_below := balanced_GS_below_sInf_of_argmin
    hJ_star 1 M_balanced M_chosen lam' D' hM_chosen_cross h_argmin
    (strict_gap_all_M_below_sInf_of_argmin hJ_star 1 M_balanced M_chosen lam' D'
      hM_chosen_cross h_argmin)
  -- Apply capstone v3' hne (PR #4009).
  exact spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing_hne
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M_chosen h_balanced hM_chosen_centered_ne hlam'_lb hlam'_ub hD'
    hM_chosen_cross h_strict_chosen axiom_GS_at_SU2 h_below

end LatticeSystem.Quantum

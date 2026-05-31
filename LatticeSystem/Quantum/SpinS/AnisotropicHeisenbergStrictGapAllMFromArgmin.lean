import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedBelowFromArgmin

/-!
# Strict gap holds for all `M'` at `t' < sInf M_chosen` (case split on `M'` crossing)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

Discharges the "strict gap at t' for all M'" hypothesis of PR #4002
(`balanced_GS_below_sInf_of_argmin`) by case-splitting on whether
`perMCrossingSet M' ∩ Icc 0 1` is non-empty:
- If non-empty: argmin property gives `sInf M_chosen ≤ sInf M'`, so
  `t' < sInf M_chosen ≤ sInf M'`, hence strict gap holds at `t'` (PR #3995).
- If empty: `perMCrossingSet M'` excludes all of `Icc 0 1`, so for `t' ∈ Icc 0 1`,
  `E_M'(γ(t')) > E_balanced(γ(t'))` strictly (negation of the set definition).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Strict gap holds for all `M' ≠ M_balanced` (non-empty) at `t' < sInf M_chosen`**:
case split on whether `perMCrossingSet M' ∩ Icc 0 1` is non-empty. -/
theorem strict_gap_all_M_below_sInf_of_argmin
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M_chosen : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M_chosen)]
    [Nonempty (Λ → Fin (N + 1))]
    (lam' D' : ℝ)
    (hne_chosen :
      (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1).Nonempty)
    (h_argmin :
      ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ N M'), M' ≠ M_balanced →
        (perMCrossingSet (Λ := Λ) hJ N M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1).Nonempty →
        sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1) ≤
        sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1)) :
    ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ N M'), M' ≠ M_balanced → ∀ t' : ℝ,
      t' ∈ Icc (0 : ℝ) 1 →
      t' < sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1) →
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D' t' <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M' lam' D' t' := by
  intro M' hNE_M' hne_eq_M' t' ht'_in_Icc ht'_lt_sInf
  by_cases h_M'_ne : (perMCrossingSet (Λ := Λ) hJ N M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1).Nonempty
  · -- Non-empty M' set: argmin gives sInf M_chosen ≤ sInf M', so t' < sInf M'.
    have h_le := h_argmin M' hNE_M' hne_eq_M' h_M'_ne
    have ht'_lt_M' : t' < sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1) :=
      lt_of_lt_of_le ht'_lt_sInf h_le
    exact strict_per_M_gap_of_lt_sInf_perMCrossingSet
      hJ N M_balanced M' lam' D' h_M'_ne ht'_in_Icc ht'_lt_M'
  · -- Empty M' set: no t ∈ Icc 0 1 has E_M' ≤ E_balanced, so strict gap holds at t'.
    rw [Set.not_nonempty_iff_eq_empty] at h_M'_ne
    -- t' ∈ Icc 0 1. If E_M'(γ(t')) ≤ E_balanced(γ(t')), then t' ∈ perMCrossingSet ∩ Icc 0 1
    -- = ∅. Contradiction.
    by_contra h_not_strict
    push_neg at h_not_strict
    have h_t'_in : t' ∈ perMCrossingSet (Λ := Λ) hJ N M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1 :=
      ⟨h_not_strict, ht'_in_Icc⟩
    rw [h_M'_ne] at h_t'_in
    exact h_t'_in

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMStrictGapBelowFirstCrossing
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedIsGSAtSU2
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedGSSetClosed

/-!
# Balanced IS GS below `sInf (perMCrossingSet M_chosen)` from argmin property

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

Discharges the "below-sInf balanced IS GS" hypothesis of capstone v3 (PR #4001)
under the **argmin property**: `M_chosen` minimises per-`M` first crossings
across all `M ≠ M_balanced` (with non-empty `magConfigS`).

For `t' < sInf (perMCrossingSet M_chosen)`, the argmin property gives
`t' < sInf (perMCrossingSet M')` for all `M'`, hence strict per-`M'` gap holds
(PR #3995) for all `M' ≠ M_balanced`. Apply PR #3990 to conclude balanced IS GS
at `γ(t')`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Balanced IS GS at `γ(t')` for `t' < sInf (perMCrossingSet M_chosen)`,
under the argmin property**: `M_chosen` minimises per-`M` first crossings
across all `M ≠ M_balanced` (non-empty), so `t' < sInf` for all such `M`,
hence strict gap holds for all `M'` at `t'`, hence balanced IS GS. -/
theorem balanced_GS_below_sInf_of_argmin
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M_chosen : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M_chosen)]
    [Nonempty (Λ → Fin (N + 1))]
    (lam' D' : ℝ)
    -- The per-M_chosen crossing set is non-empty (in Icc 0 1).
    (hne_chosen :
      (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1).Nonempty)
    -- Argmin property: M_chosen minimises per-M first crossings across M ≠ M_balanced.
    (_h_argmin :
      ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ N M'), M' ≠ M_balanced →
        (perMCrossingSet (Λ := Λ) hJ N M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1).Nonempty →
        sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1) ≤
        sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1))
    -- "Every M' ≠ M_balanced (non-empty) has a crossing in Icc 0 1" — required to apply
    -- strict_per_M_gap. For M' with no crossing, the strict gap trivially holds
    -- at all t' ∈ Icc 0 1.
    (h_all_M_crossing_or_no_violation :
      ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ N M'), M' ≠ M_balanced → ∀ t' : ℝ,
        t' ∈ Icc (0 : ℝ) 1 →
        t' < sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1) →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ N M_balanced lam' D' t' <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ N M' lam' D' t') :
    ∀ t' : ℝ, t' ∈ Ico (0 : ℝ)
        (sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1)) →
      t' ∈ balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' := by
  intro t' ht'_mem
  -- t' ∈ Icc 0 1.
  have h_t_first_le_1 :
      sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1) ≤ 1 := by
    obtain ⟨x, hx⟩ := hne_chosen
    exact le_trans (csInf_le
      (bddBelow_perMCrossingSet_inter_Icc hJ N M_balanced M_chosen lam' D') hx) hx.2.2
  have ht'_in_Icc : t' ∈ Icc (0 : ℝ) 1 :=
    ⟨ht'_mem.1, le_trans (le_of_lt ht'_mem.2) h_t_first_le_1⟩
  -- For all M' ≠ M_balanced (non-empty), strict gap at γ(t').
  have h_strict_all_M : ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ N M'), M' ≠ M_balanced →
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D' t' <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M' lam' D' t' := by
    intro M' hNE_M' hne_eq_M'
    exact h_all_M_crossing_or_no_violation M' hNE_M' hne_eq_M' t' ht'_in_Icc ht'_mem.2
  -- Apply PR #3990: balanced IS GS at γ(t').
  unfold balancedGSSet
  simp only [Set.mem_setOf_eq]
  -- Use PR #3990 to get sector-M_balanced min = global Ĥ min at γ(t').
  exact hermitianMinEigenvalue_balanced_eq_full_of_strict_gap
    (Λ := Λ) hJ N M_balanced
    (anisotropicHeisenbergParametricPath lam' D' t').1
    (anisotropicHeisenbergParametricPath lam' D' t').2
    h_strict_all_M

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedMinEqFullAtSInf
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMCrossingEqualityAtSInf
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorGroundEigenvector
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfFinrankLeTwoAtPath
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergCrossingContradictionConditional
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPathStaysInRegion

/-!
# Spin-1/2 Tasaki §2.5 Theorem 2.4 obligation (2) — capstone v3 (sup-analysis crossing)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

★ Third reformulation of the obligation (2) capstone, replacing #3980's
"first-crossing identification" axiom (path-wide) with the **single-`M` argmin
sup-analysis** hypothesis. The crossing point is extracted from the per-`M`
crossing set (`sInf`-based, PRs #3994/#3998/#3999) rather than the IVT crossing
of PR #3978, giving a TIGHTER capstone where:

- The strict gap at `(1, 0)` is supplied (`(2-IVT-c)` axiom; deferred).
- The "below-sInf strict gap" is supplied as a `balancedGSSet`-membership
  hypothesis (the remaining Finset-iteration work for the argmin choice).

Composes:
- PR #3999 `balanced_min_eq_full_at_sInf` (E_balanced = global Ĥ min at sInf).
- PR #3998 `anisotropicHeisenbergS_per_M_crossing_equality_at_sInf` (E_M = E_balanced at sInf).
- PR #3963 sector ground full-eigenvector existence.
- PR #3976 spin-1/2 finrank ≤ 2 at global min along path.
- PR #3966 embedded two-sector contradiction.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 obligation (2) capstone v3 (sup-analysis crossing)**: derives
False from the contradiction hypothesis `E_M(λ', D') ≤ E_balanced(λ', D')` via
the per-`M` first-crossing sup analysis, under:
- spin-1/2 obligation (1) hypotheses (PR #3970 family),
- strict-GS axiom at `(1, 0)` and at the strict-gap-at-(1, 0),
- "below-sInf balanced IS GS" hypothesis (argmin choice).

The conclusion is `False` (since we assumed obligation 2 violated). -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing
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
    -- Contradiction hypothesis: E_M ≤ E_balanced at (λ', D').
    (h_violation :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1)
    -- Strict gap at (1, 0).
    (h_strict_gap_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M lam' D' 0)
    -- Strict-GS axiom at (1, 0): combined with PR #3990 it would discharge to the strict gap,
    -- but for now passed in directly.
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1
          (anisotropicHeisenbergParametricPath lam' D' 0).1
          (anisotropicHeisenbergParametricPath lam' D' 0).2))
    -- "Below-sInf balanced IS GS" hypothesis (the remaining Finset-iteration gap).
    (h_balanced_GS_below : ∀ t' : ℝ, t' ∈ Ico (0 : ℝ)
        (sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)) →
      t' ∈ balancedGSSet (Λ := Λ) hJ_star 1 M_balanced lam' D') :
    False := by
  classical
  -- Extract the per-M sup-crossing point t.
  set hne : (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1).Nonempty := by
    exact ⟨1, h_violation, ⟨by norm_num, le_refl _⟩⟩
  set t := sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)
    with ht_def
  -- t ∈ Icc 0 1.
  have hmem : t ∈ perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1 :=
    sInf_perMCrossingSet_inter_Icc_mem hJ_star 1 M_balanced M lam' D' hne
  have ht_nn : 0 ≤ t := hmem.2.1
  have ht_le : t ≤ 1 := hmem.2.2
  -- 0 < t (from strict gap at (1, 0) ruling out the t = 0 case).
  have ht_pos : 0 < t := by
    rcases lt_or_eq_of_le ht_nn with hpos | h0_eq
    · exact hpos
    · exfalso
      -- t = 0 + crossing membership ⟹ E_M(γ(0)) ≤ E_balanced(γ(0)), contradicting strict gap.
      have h_in := hmem.1
      simp only [perMCrossingSet, Set.mem_setOf_eq] at h_in
      rw [← h0_eq] at h_in
      linarith
  -- E_M(γ(t)) = E_balanced(γ(t)) (PR #3998).
  have h_eq_at_t := anisotropicHeisenbergS_per_M_crossing_equality_at_sInf
    hJ_star 1 M_balanced M lam' D' hne h_strict_gap_SU2
  -- E_balanced(γ(t)) = global Ĥ min(γ(t)) (PR #3999). Convert to unfolded form.
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
  -- Get sector ground eigenvectors at γ(t).
  obtain ⟨Φ_bal, hΦ_bal_ne, hΦ_bal_eig, hΦ_bal_mem⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 1 M_balanced
  obtain ⟨Φ_M, hΦ_M_ne, hΦ_M_eig, hΦ_M_mem⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 1 M
  -- Rewrite via h_eq_at_t to express E_M at γ(t) as E_balanced at γ(t).
  -- h_eq_at_t : E_M(γ(t)) = E_balanced(γ(t)) (in the named-def form).
  -- hΦ_M_eig coeff is hermitianMinEigenvalue ... at M (sector M min at γ(t)).
  -- This IS the unfolded form of anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath.
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
  -- Apply PR #3976 + PR #3966 contradiction.
  have h_finrank :=
    spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_path
      A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
      hlam'_lb hlam'_ub hD' ht_pos ht_le
  -- The hΦ_M_eig is now at E_balanced(γ(t)). We need to express it at the global min, same as Φ_bal.
  -- E_balanced(γ(t)) = global Ĥ min(γ(t)) by h_bal_eq_full.
  -- But hΦ_M_eig coeff is E_balanced(γ(t)) (after the rewrite); rewrite further to global min.
  rw [h_bal_eq_full] at hΦ_M_eig
  exact anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two
    J ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
      ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) _
    h_finrank hΦ_bal_ne h_balanced hΦ_bal_eig
    hΦ_M_ne hM_ne_balanced hΦ_M_eig

end LatticeSystem.Quantum

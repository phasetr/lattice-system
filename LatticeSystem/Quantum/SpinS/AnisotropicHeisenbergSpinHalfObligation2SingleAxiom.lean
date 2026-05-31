import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfObligation2AxiomaticFinal
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGSAtSU2FromStrictGap

/-!
# Spin-1/2 Tasaki §2.5 Theorem 2.4 obligation (2) — single-axiom capstone

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

★★★★ The ABSOLUTE FINAL composed capstone — reduces spin-1/2 obligation (2) to
a **single mathematical axiom**: the strict gap at `(1, 0)` for all
`M ≠ M_balanced` (non-empty).

Composes PR #4010 (`spinHalf_anisotropicHeisenbergS_obligation_2_final`,
2-axiom version) with PR #4013 (`strict_GS_at_path_zero_from_strict_gap_at_SU2`,
which discharges axiom 2 from axiom 1).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **★★★★ ULTIMATE CAPSTONE**: spin-1/2 obligation (2) under a single
mathematical axiom — the strict gap at `(1, 0)` for all `M ≠ M_balanced`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_single_axiom
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
    -- ★ The ONLY mathematical axiom: strict gap at (1, 0) for all valid M' ≠ M_balanced.
    (axiom_strict_gap_at_SU2 :
      ∀ M' : ℕ, [Nonempty (magConfigS Λ 1 M')] → M' ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M' lam' D' 0) :
    False := by
  -- Derive the strict-GS axiom at (1, 0) from the strict-gap axiom via PR #4013.
  have axiom_GS_at_SU2 :=
    strict_GS_at_path_zero_from_strict_gap_at_SU2 (Λ := Λ) hJ_star 1 M_balanced
      lam' D' (fun M' _ hne => by
        haveI := ‹Nonempty (magConfigS Λ 1 M')›
        -- The strict-gap axiom is in the named-def form; convert via path_zero unfolding.
        have := axiom_strict_gap_at_SU2 M' hne
        unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at this
        have hpath := anisotropicHeisenbergParametricPath_zero lam' D'
        simp only [hpath] at this
        exact this)
  -- Apply PR #4010's capstone v5.
  exact spinHalf_anisotropicHeisenbergS_obligation_2_final
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig
    axiom_strict_gap_at_SU2 axiom_GS_at_SU2

end LatticeSystem.Quantum

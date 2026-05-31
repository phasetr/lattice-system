import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfObligation2AxiomaticV3
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedBelowFromArgmin
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGapAllMFromArgmin

/-!
# Spin-1/2 Tasaki §2.5 Theorem 2.4 obligation (2) — capstone v4 (argmin discharged)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

★ Fourth reformulation: discharges PR #4001's "below-sInf balanced IS GS"
hypothesis using PRs #4002 (`balanced_GS_below_sInf_of_argmin`) + #4003
(`strict_gap_all_M_below_sInf_of_argmin`), reducing the capstone to two
explicit axioms:

1. (2-IVT-c) strict gap at `(1, 0)`.
2. Strict-GS axiom at `(1, 0)` (equiv. to "balanced IS GS at γ(0)").
3. **Argmin property**: `M_chosen` minimises per-`M` first crossings across
   `M ≠ M_balanced` (non-empty).

The argmin property is the LAST structural input. To make it unconditional,
a Finset iteration extracting the actual argmin of `t_first_M` over the
finite set of `M ≠ M_balanced` (non-empty) values is needed (deferred to
a follow-up PR).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 obligation (2) capstone v4 (argmin discharged)**: derives False
under the contradiction hypothesis + obligation (1) hypotheses + 3 axioms. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic_argmin
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
    (h_violation :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1)
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
    -- ★ Argmin axiom: M minimises per-M' first crossings across M' ≠ M_balanced.
    (h_argmin :
      ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ 1 M'), M' ≠ M_balanced →
        (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1).Nonempty →
        sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1) ≤
        sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1)) :
    False := by
  -- Set up: M is the argmin, perMCrossingSet M is non-empty (from violation).
  have hne : (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1).Nonempty :=
    ⟨1, h_violation, ⟨by norm_num, le_refl _⟩⟩
  -- Discharge PR #4001's "below-sInf balanced IS GS" hypothesis via #4002 + #4003.
  have h_below := balanced_GS_below_sInf_of_argmin
    hJ_star 1 M_balanced M lam' D' hne h_argmin
    (strict_gap_all_M_below_sInf_of_argmin hJ_star 1 M_balanced M lam' D' hne h_argmin)
  -- Apply PR #4001's capstone v3.
  exact spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M h_balanced hM_ne_balanced hlam'_lb hlam'_ub hD'
    h_violation h_strict_gap_SU2 h_GS_at_SU2 h_below

end LatticeSystem.Quantum

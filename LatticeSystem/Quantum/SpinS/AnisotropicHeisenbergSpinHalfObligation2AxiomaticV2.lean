import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfObligation2Axiomatic
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedIsGSAtSU2

/-!
# Spin-1/2 Tasaki §2.5 Theorem 2.4 obligation (2) — capstone v2 (strict-gap path-wide)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Reformulation of PR #3980's axiomatic capstone using a single, more interpretable
axiom: **strict gap at every path point** `γ(t) for t ∈ [0, 1]` (rather than
two separate axioms for the SU(2) point + first-crossing identification).

Discharges PR #3980's second axiom (first-crossing identification) via PR #3990
(balanced is GS from strict gap at a single point), applied path-wise.

The remaining axiom (strict gap at every `γ(t)`) is strictly stronger than the
(2-IVT-c) strict gap at `(1, 0)` axiom alone — it asserts the GS-is-balanced
property is path-stable from `(1, 0)` to `(λ', D')`. The IVT crossing argument
(PR #3978) would derive a contradiction if strict gap fails somewhere along
the path, but proving path-wide stability from `(1, 0)` strict gap requires
the FULL first-crossing sup analysis (deferred).

This reformulation makes the remaining work explicit: prove "strict gap at γ(t)
for t ∈ (0, 1]" from "strict gap at (1, 0)" via continuity + IVT crossing.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 obligation (2) capstone v2 (strict-gap path-wide)**: under the
spin-1/2 obligation (1) hypotheses and a **path-wide strict gap** axiom (replacing
PR #3980's two separate axioms), the obligation (2) conclusion holds at `(λ', D')`. -/
@[deprecated "Use the canonical capstone spinHalf_anisotropicHeisenbergS_obligation_2_single_axiom (PR #4014). This v2 capstone is an orphan in the final dependency chain." (since := "2026-05-31")]
theorem spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic_path_wide
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
    (M_balanced : ℕ) (M : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_ne_balanced :
      (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    -- Strict-gap path-wide axiom (replaces PR #3980's two separate axioms).
    (axiom_strict_gap_path_wide :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ 1 M'), M' ≠ M_balanced →
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := 1) (M := M_balanced) hJ_star
              (anisotropicHeisenbergParametricPath lam' D' t).1
              (anisotropicHeisenbergParametricPath lam' D' t).2) <
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := 1) (M := M') hJ_star
              (anisotropicHeisenbergParametricPath lam' D' t).1
              (anisotropicHeisenbergParametricPath lam' D' t).2)) :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') <
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M) hJ_star lam' D') := by
  -- Strict gap at t = 0 from the path-wide axiom.
  have h_strict_gap_at_zero :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star 1 0) <
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M) hJ_star 1 0) := by
    have := axiom_strict_gap_path_wide 0 (by norm_num) M inferInstance
      (fun h => hM_ne_balanced (by rw [h, h_balanced]))
    rw [anisotropicHeisenbergParametricPath_zero] at this
    exact this
  -- First-crossing identification from path-wide strict gap via PR #3990.
  have h_first_crossing :
      ∀ t : ℝ, 0 < t → t ≤ 1 →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := 1) (M := M_balanced) hJ_star
            (anisotropicHeisenbergParametricPath lam' D' t).1
            (anisotropicHeisenbergParametricPath lam' D' t).2) =
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := 1) hJ_star
            (show star ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ) =
                ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ) from by
              rw [Complex.star_def, Complex.conj_ofReal])
            (show star ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) =
                ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) from by
              rw [Complex.star_def, Complex.conj_ofReal])) := by
    intro t ht_pos ht_le
    -- Strict gap at γ(t) (path-wide axiom).
    have h_strict_t := fun M' (hNE : Nonempty (magConfigS Λ 1 M')) (hne : M' ≠ M_balanced) =>
      axiom_strict_gap_path_wide t ⟨le_of_lt ht_pos, ht_le⟩ M' hNE hne
    -- Apply PR #3990: balanced is GS at γ(t).
    have := hermitianMinEigenvalue_balanced_eq_full_of_strict_gap
      (Λ := Λ) hJ_star 1 M_balanced
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2
      h_strict_t
    exact this
  -- Apply PR #3980 with the discharged axioms.
  exact spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M h_balanced hM_ne_balanced hlam'_lb hlam'_ub hD'
    h_strict_gap_at_zero h_first_crossing

end LatticeSystem.Quantum

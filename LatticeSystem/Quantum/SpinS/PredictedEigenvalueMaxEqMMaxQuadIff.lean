import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxCanonicalComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormEqMMaxIff
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLeMMax

/-!
# Unified max iff: `max(canonical, complement) = m_max·(m_max+1) ↔ saturated edge`

PR #2966 gave `max(canonical, complement) = ‖biw‖·(‖biw‖+1)`.

PR #2969 gave `‖biw‖ = m_max ↔ saturated edge` at `N ≥ 1`.

Combining: at `N ≥ 1`,

  `max(canonical, complement) = m_max·(m_max+1) ↔ |A| = 0 ∨ |¬A| = 0`.

The **physical** predicted `(Ŝ_tot)²` eigenvalue (max over orientations)
attains the fully-polarised ferromagnetic value `m_max·(m_max+1)`
**iff** the configuration is at a saturated edge.

This unifies PR #2948 (canonical iff at `|¬A| = 0`) and PR #2956
(complement iff at `|A| = 0`) into a single orientation-free iff using
the physical `max` quantity.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Unified max iff**: `max(canonical, complement) = m_max·(m_max+1) ↔
saturated edge** at `N ≥ 1`. Unifies PR #2948 / PR #2956 via PR #2966 +
PR #2969. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_mMax_quad_iff_saturated
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    max
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)).re
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_norm_quad
        A N]
  -- ‖biw‖·(‖biw‖+1) = m_max(m_max+1) ↔ ‖biw‖ = m_max (using ‖biw‖ ∈ [0, m_max]).
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  have hbiw_le : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 :=
    bipartiteImbalanceWeight_norm_le_mMax A N
  rw [show ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
        (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ + 1) =
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
          ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) ↔
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
          (Fintype.card Λ : ℝ) * (N : ℝ) / 2 from by
      constructor
      · intro heq
        -- x(x+1) = m(m+1) and x ∈ [0, m] ⟹ x = m.
        -- Factor: (x - m)(x + m + 1) = 0.
        have hfact : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
            (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ + 1) -
              (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
                ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) =
            (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
                (Fintype.card Λ : ℝ) * (N : ℝ) / 2) *
              (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
                (Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by ring
        have hzero : (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
                (Fintype.card Λ : ℝ) * (N : ℝ) / 2) *
              (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
                (Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) = 0 := by linarith
        rcases mul_eq_zero.mp hzero with h1 | h2
        · linarith
        · -- ‖biw‖ + m_max + 1 = 0, but ‖biw‖ ≥ 0 and m_max ≥ 0 ⟹ contradiction.
          nlinarith
      · intro h
        rw [h]]
  exact bipartiteImbalanceWeight_norm_eq_mMax_iff_saturated A N hN

end LatticeSystem.Quantum

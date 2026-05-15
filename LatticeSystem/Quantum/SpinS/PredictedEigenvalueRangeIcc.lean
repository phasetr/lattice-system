import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueReNonneg
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueLeMMaxQuad

/-!
# Predicted `(Ŝ_tot)²` eigenvalue range: `[0, m_max·(m_max + 1)]`

At the proper orientation `|¬A| ≤ |A|`:

  `0 ≤ predicted (Ŝ_tot)² eigenvalue ≤ m_max·(m_max + 1)`.

The lower bound is PR #2935 (non-negativity); the upper bound is PR
#2942 (≤ `m_max·(m_max+1)`). Combining them gives the closed-interval
characterisation of the predicted Casimir spectrum.

Endpoints:
- Lower endpoint `0` attained at balanced `|A| = |¬A|` (PR #2939
  via biw.re = 0).
- Upper endpoint `m_max·(m_max+1)` attained at saturated `|¬A| = 0`
  (PR #2938).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Range characterisation of predicted (Ŝ_tot)² eigenvalue**:
`∈ [0, m_max·(m_max + 1)]` at proper orientation `|¬A| ≤ |A|`. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_mem_Icc_of_cardNotA_le_cardA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re ∈
      Set.Icc (0 : ℝ)
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
          ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1)) := by
  refine ⟨?_, ?_⟩
  · exact bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_nonneg_of_cardNotA_le_cardA
      A N horient
  · exact bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_le_mMax_quad_of_cardNotA_le_cardA
      A N horient

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueReNonnegComplement
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueComplementLeMMaxQuad

/-!
# Complement predicted `(Ŝ_tot)²` eigenvalue range: `[0, m_max·(m_max + 1)]`

At the complement orientation `|A| ≤ |¬A|`:

  `0 ≤ complement predicted (Ŝ_tot)² eigenvalue ≤ m_max·(m_max + 1)`.

Mirror of PR #2950. The lower bound is PR #2951 (non-negativity);
the upper bound is PR #2943.

Endpoints:
- Lower endpoint `0` attained at balanced `|A| = |¬A|` (PR #2939
  via biw.re = 0; same value in complement form).
- Upper endpoint `m_max·(m_max+1)` attained at complement-saturated
  `|A| = 0` (PR #2941).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Range characterisation of complement predicted (Ŝ_tot)² eigenvalue**:
`∈ [0, m_max·(m_max + 1)]` at complement orientation `|A| ≤ |¬A|`.
Mirror of PR #2950. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_mem_Icc_of_cardA_le_cardNotA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re ∈
      Set.Icc (0 : ℝ)
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
          ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1)) := by
  refine ⟨?_, ?_⟩
  · exact bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_nonneg_of_cardA_le_cardNotA
      A N horient
  · exact bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_le_mMax_quad_of_cardA_le_cardNotA
      A N horient

end LatticeSystem.Quantum

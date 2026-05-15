import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceNorm
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormSaturated

/-!
# Predicted `(Ŝ_tot)²` eigenvalue at saturated: `m_max·(m_max + 1)`

PR #2930 gave the eigenvalue identification at `|¬A| ≤ |A|`:
`((s_A − s_B)·((s_A − s_B) + 1)).re = ‖biw‖·(‖biw‖ + 1)`.

At saturated `|¬A| = 0`, `‖biw‖ = |Λ|·N/2 = m_max`
(PR #2851 `bipartiteImbalanceWeight_norm_eq_mMax_of_cardNotA_zero`).
Substituting:

  `predicted (Ŝ_tot)² eigenvalue = m_max·(m_max + 1)`
  at `|¬A| = 0`.

The predicted GS at saturated edges has the fully-polarised
ferromagnetic Casimir value `m_max(m_max+1)`, as expected.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Saturated-edge predicted (Ŝ_tot)² eigenvalue = `m_max·(m_max + 1)`**. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_mMax_quad_of_cardNotA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by
  -- At |¬A| = 0, the orientation hypothesis |¬A| ≤ |A| holds trivially.
  have horient :
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
    rw [h]; exact Nat.zero_le _
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
        A N horient,
      bipartiteImbalanceWeight_norm_eq_mMax_of_cardNotA_zero A N h]
  ring

end LatticeSystem.Quantum

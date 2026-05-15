import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceNormComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormSaturated

/-!
# Complement-saturated predicted `(Ŝ_tot)²` eigenvalue: `m_max·(m_max + 1)`

PR #2931 gave the complement-orientation eigenvalue at `|A| ≤ |¬A|`:
`((s_B − s_A)·((s_B − s_A) + 1)).re = ‖biw‖·(‖biw‖ + 1)`.

At saturated complement `|A| = 0`, `‖biw‖ = |Λ|·N/2 = m_max`
(PR #2852 `bipartiteImbalanceWeight_norm_eq_mMax_of_cardA_zero`).
Substituting:

  `complement predicted (Ŝ_tot)² eigenvalue = m_max·(m_max + 1)`
  at `|A| = 0`.

Mirror of PR #2938. The complement-orientation predicted GS at
saturated complement also has the fully-polarised ferromagnetic
Casimir value.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Complement saturated predicted (Ŝ_tot)² eigenvalue
= `m_max·(m_max + 1)`** at `|A| = 0`. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_mMax_quad_of_cardA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by
  have horient :
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    rw [h]; exact Nat.zero_le _
  rw [bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
        A N horient,
      bipartiteImbalanceWeight_norm_eq_mMax_of_cardA_zero A N h]
  ring

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceNormComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormEqZero

/-!
# Complement predicted `(Ŝ_tot)²` eigenvalue = 0 ↔ balanced (at `|A| ≤ |¬A|`, `N ≥ 1`)

PR #2931 gave the complement eigenvalue identification at
`|A| ≤ |¬A|`:
`((s_B − s_A)·((s_B − s_A) + 1)).re = ‖biw‖·(‖biw‖ + 1)`.

This vanishes iff `‖biw‖ = 0` (since `‖biw‖ + 1 ≥ 1 > 0`). At
`N ≥ 1`, `‖biw‖ = 0 ↔ |A| = |¬A|` (PR #2855). Hence

  `complement predicted (Ŝ_tot)² eigenvalue = 0 ↔ |A| = |¬A|`
  at `|A| ≤ |¬A|`, `N ≥ 1`.

Mirror of PR #2936.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Complement predicted (Ŝ_tot)² eigenvalue = 0 ↔ balanced** at
`|A| ≤ |¬A|`, `N ≥ 1`. Mirror of PR #2936. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_zero_iff_balanced_of_cardA_le_cardNotA
    (A : Λ → Bool) {N : ℕ} (hN : 1 ≤ N)
    (horient : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  rw [bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
        A N horient]
  -- Goal: ‖biw‖·(‖biw‖+1) = 0 ↔ |A| = |¬A|.
  constructor
  · intro h
    have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
      norm_nonneg _
    have hfact :
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
              ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
            ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
            (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ + 1) := by ring
    rw [hfact] at h
    have hbiw_plus_one_pos :
        0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ + 1 := by linarith
    have hbiw_zero : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = 0 := by
      rcases mul_eq_zero.mp h with h0 | h1
      · exact h0
      · linarith
    exact (bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq (Λ := Λ) A hN).mp
      hbiw_zero
  · intro h
    have hbiw_zero : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = 0 :=
      (bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq (Λ := Λ) A hN).mpr h
    rw [hbiw_zero]
    ring

end LatticeSystem.Quantum

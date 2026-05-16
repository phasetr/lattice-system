import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgComplementReNegIff

/-!
# `(pmA).re + (pm¬A).re < 0 ↔ |Λ| ≥ 1 ∧ N ≥ 1`

Multiplying the avg iff (PR #3080) by 2:

  `(predicted_min A).re + (predicted_min ¬A).re < 0
   ↔ 0 < |Λ| ∧ 0 < N`.

Iff version of PR #3076 (forward direction).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **sum iff strict negativity ↔ `|Λ| ≥ 1 ∧ N ≥ 1`**. -/
theorem bipartiteToyMinEnergyPredicted_sum_complement_re_neg_iff_card_pos
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re < 0 ↔
      0 < Fintype.card Λ ∧ 0 < N := by
  have havg_iff := bipartiteToyMinEnergyPredicted_avg_complement_re_neg_iff_card_pos
    (Λ := Λ) A N
  constructor
  · intro hlt
    have havg_lt : ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 < 0 := by
      linarith
    exact havg_iff.mp havg_lt
  · intro hcond
    have havg_lt := havg_iff.mpr hcond
    linarith

end LatticeSystem.Quantum

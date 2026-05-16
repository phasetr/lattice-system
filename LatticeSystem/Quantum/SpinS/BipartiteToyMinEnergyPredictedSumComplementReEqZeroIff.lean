import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgComplementReEqZeroIff

/-!
# `(pmA).re + (pm¬A).re = 0 ↔ |Λ| = 0 ∨ N = 0`

Multiplying PR #3088 (avg = 0 iff) by 2:

  `(predicted_min A).re + (predicted_min ¬A).re = 0
   ↔ |Λ| = 0 ∨ N = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **sum = 0 iff `|Λ| = 0 ∨ N = 0`** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_sum_complement_re_eq_zero_iff_card_zero
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 ↔
      Fintype.card Λ = 0 ∨ N = 0 := by
  have havg_iff := bipartiteToyMinEnergyPredicted_avg_complement_re_eq_zero_iff_card_zero
    (Λ := Λ) A N
  constructor
  · intro heq
    have havg_eq : ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 = 0 := by
      linarith
    exact havg_iff.mp havg_eq
  · intro hor
    have havg_eq := havg_iff.mpr hor
    linarith

end LatticeSystem.Quantum

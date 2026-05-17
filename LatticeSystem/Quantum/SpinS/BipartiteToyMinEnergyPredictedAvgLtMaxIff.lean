import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinLtAvgIff
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxAddMinEqTwoAvg

/-!
# `avg < max((pmA).re, (pm¬A).re) ↔ |A| ≠ |¬A|` at `N ≥ 1`

Upper companion of PR #3040 (`min < avg ↔ unbalanced`). At `N ≥ 1`:

  `((predicted_min A).re + (predicted_min ¬A).re) / 2
   < max((predicted_min A).re, (predicted_min ¬A).re) ↔ |A| ≠ |¬A|`.

Direct from PR #3127's `max + min = 2·avg`: `avg < max ↔ min < avg`
(both express off-balanced) combined with PR #3040.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg < max iff unbalanced** at `N ≥ 1`. Upper companion of PR #3040. -/
theorem bipartiteToyMinEnergyPredicted_avg_lt_max_complement_re_iff_unbalanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 <
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  -- avg < max ↔ min < avg via max + min = 2·avg, then PR #3040.
  have hsum := bipartiteToyMinEnergyPredicted_max_add_min_complement_re_eq_two_avg
    (Λ := Λ) A N
  have hmin_lt := bipartiteToyMinEnergyPredicted_min_complement_re_lt_avg_iff_unbalanced
    (Λ := Λ) A N hN
  -- avg < max ↔ 2·avg < 2·max ↔ min + max < 2·max ↔ min < max ↔ min < avg.
  -- Simpler: avg < max ↔ avg - max < 0 ↔ -(max - avg) < 0 ↔ 0 < max - avg.
  -- And from max + min = 2·avg, max - avg = avg - min. So avg < max ↔ min < avg.
  have hequiv : ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 <
        max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hequiv]
  exact hmin_lt

end LatticeSystem.Quantum

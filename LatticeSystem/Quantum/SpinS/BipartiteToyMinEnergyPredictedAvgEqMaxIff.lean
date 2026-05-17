import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinEqAvgIff
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxAddMinEqTwoAvg

/-!
# `avg = max((pmA).re, (pm¬A).re) ↔ |A| = |¬A|` at `N ≥ 1`

Equality companion of PR #3141. At `N ≥ 1`:

  `((predicted_min A).re + (predicted_min ¬A).re) / 2
   = max((predicted_min A).re, (predicted_min ¬A).re) ↔ |A| = |¬A|`.

Direct from PR #3127's `max + min = 2·avg`: `avg = max ↔ min = avg`
(both express balanced) combined with the existing iff `min = avg ↔ balanced`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg = max iff balanced** at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_avg_eq_max_complement_re_iff_balanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 =
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hsum := bipartiteToyMinEnergyPredicted_max_add_min_complement_re_eq_two_avg
    (Λ := Λ) A N
  have hmin_eq := bipartiteToyMinEnergyPredicted_min_complement_re_eq_avg_iff_balanced
    (Λ := Λ) A N hN
  -- avg = max ↔ min = avg via max + min = 2·avg.
  have hequiv : ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 =
        max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hequiv]
  exact hmin_eq

end LatticeSystem.Quantum

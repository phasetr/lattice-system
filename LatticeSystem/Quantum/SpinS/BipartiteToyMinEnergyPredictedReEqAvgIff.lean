import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReEqComplementReIff

/-!
# `(pmA).re = avg ↔ |A| = |¬A|` at `N ≥ 1`

The canonical predicted-min energy `(pmA).re` equals the orientation-pair
average exactly at balanced. At `N ≥ 1`:

  `(predicted_min A).re = ((predicted_min A).re + (predicted_min ¬A).re) / 2
   ↔ |A| = |¬A|`.

Direct from `x = (x + y) / 2 ↔ x = y` composed with PR #3066.
At balanced both `(pmA).re` and `(pm¬A).re` coincide with the avg.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pmA).re = avg iff `|A| = |¬A|`** at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_re_eq_avg_complement_re_iff_balanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hbal := bipartiteToyMinEnergyPredicted_re_eq_complement_re_iff_balanced
    (Λ := Λ) A N hN
  -- x = (x + y) / 2 ↔ x = y for reals.
  have hmidpoint : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hmidpoint]
  exact hbal

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLtComplementReIff

/-!
# `(pmA).re < max((pmA).re, (pm¬A).re) ↔ |A| < |¬A|` at `N ≥ 1`

The canonical predicted-min energy `(pmA).re` sits strictly below the
orientation-pair max exactly when `A` is strictly lighter than `¬A`.
At `N ≥ 1`:

  `(predicted_min A).re < max((predicted_min A).re, (predicted_min ¬A).re)
   ↔ |A| < |¬A|`.

Direct from `x < max x y ↔ x < y` composed with PR #3067.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pmA).re < max iff `|A| < |¬A|`** at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_re_lt_max_complement_re_iff_cardA_lt_cardNotA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re <
        max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hlt := bipartiteToyMinEnergyPredicted_re_lt_complement_re_iff_cardA_lt_cardNotA
    (Λ := Λ) A N hN
  -- x < max x y ↔ x < y.
  rw [lt_max_iff]
  constructor
  · intro h
    rcases h with hxx | hxy
    · exact absurd hxx (lt_irrefl _)
    · exact hlt.mp hxy
  · intro hcard
    exact Or.inr (hlt.mpr hcard)

end LatticeSystem.Quantum

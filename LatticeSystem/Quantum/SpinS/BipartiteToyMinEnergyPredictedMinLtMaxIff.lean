import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReEqComplementReIff

/-!
# `min((pmA).re, (pm¬A).re) < max((pmA).re, (pm¬A).re) ↔ |A| ≠ |¬A|` at `N ≥ 1`

The orientation min and max coincide exactly when the orientation pair
is balanced. At `N ≥ 1`:

  `min((predicted_min A).re, (predicted_min ¬A).re)
   < max((predicted_min A).re, (predicted_min ¬A).re)
   ↔ |A| ≠ |¬A|`.

Equivalently, the orientation spread `max − min = 2·‖biw‖` is positive
exactly off-balanced (PR #3122 establishes `spread = 2·‖biw‖`, and
`‖biw‖ > 0 ↔ |A| ≠ |¬A|` at `N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min < max iff `|A| ≠ |¬A|`** at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_min_lt_max_complement_re_iff_unbalanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hbal := bipartiteToyMinEnergyPredicted_re_eq_complement_re_iff_balanced
    (Λ := Λ) A N hN
  constructor
  · intro hlt hcard
    -- |A| = |¬A| → pmA.re = pm¬A.re → min = max, contradiction.
    have hre_eq : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
      hbal.mpr hcard
    rw [hre_eq, min_self, max_self] at hlt
    exact lt_irrefl _ hlt
  · intro hne
    -- |A| ≠ |¬A| → pmA.re ≠ pm¬A.re → min < max.
    have hre_ne : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≠
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
      intro hre_eq
      exact hne (hbal.mp hre_eq)
    -- min x y < max x y ↔ x ≠ y.
    rcases lt_or_gt_of_ne hre_ne with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
      exact hlt
    · rw [min_eq_right hgt.le, max_eq_left hgt.le]
      exact hgt

end LatticeSystem.Quantum

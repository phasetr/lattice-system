import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReEqComplementReIff

/-!
# `min((pmA).re, (pm¬A).re) = max((pmA).re, (pm¬A).re) ↔ |A| = |¬A|` at `N ≥ 1`

The orientation min and max coincide exactly when the orientation pair
is balanced. At `N ≥ 1`:

  `min((predicted_min A).re, (predicted_min ¬A).re)
   = max((predicted_min A).re, (predicted_min ¬A).re)
   ↔ |A| = |¬A|`.

Mirror of PR #3133 (strict `<`); the orientation pair degenerates to a
single point iff balanced. Equivalent to `‖biw‖ = 0` (spread = 0).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min = max iff `|A| = |¬A|`** at `N ≥ 1`. Mirror of PR #3133. -/
theorem bipartiteToyMinEnergyPredicted_min_eq_max_complement_re_iff_balanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hbal := bipartiteToyMinEnergyPredicted_re_eq_complement_re_iff_balanced
    (Λ := Λ) A N hN
  constructor
  · intro hmin_eq_max
    -- min x y = max x y → x = y.
    have hre_eq : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
      rcases le_total
          (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at hmin_eq_max
        exact hmin_eq_max
      · rw [min_eq_right hle, max_eq_left hle] at hmin_eq_max
        exact hmin_eq_max.symm
    exact hbal.mp hre_eq
  · intro hcard
    have hre_eq : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
      hbal.mpr hcard
    rw [hre_eq, min_self, max_self]

end LatticeSystem.Quantum

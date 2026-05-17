import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLeComplementReIff

/-!
# `(pmA).re = max((pmA).re, (pm¬A).re) ↔ |¬A| ≤ |A|` at `N ≥ 1`

The canonical predicted-min energy `(pmA).re` equals the orientation-pair
max exactly when `A` is at least as heavy as `¬A`. At `N ≥ 1`:

  `(predicted_min A).re = max((predicted_min A).re, (predicted_min ¬A).re)
   ↔ |¬A| ≤ |A|`.

Direct from `x = max x y ↔ y ≤ x` composed with PR #3070 applied to `¬A`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pmA).re = max iff `|¬A| ≤ |A|`** at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_re_eq_max_complement_re_iff_cardNotA_le_cardA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
        max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
  -- x = max x y ↔ y ≤ x.
  have hxmax_iff : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
        (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re := by
    constructor
    · intro h
      have : (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
          max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
        le_max_right _ _
      linarith [this, h]
    · intro h
      exact (max_eq_left h).symm
  rw [hxmax_iff]
  -- (pm¬A).re ≤ (pmA).re ↔ |¬A| ≤ |A|: apply PR #3070 to ¬A then fold.
  have hle := bipartiteToyMinEnergyPredicted_re_le_complement_re_iff_cardA_le_cardNotA
    (Λ := Λ) (fun x : Λ => ! A x) N hN
  have hfunext : (fun x : Λ => ! (! A x)) = A := by
    funext x; cases A x <;> simp
  rw [hfunext] at hle
  have hfilter : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases A x <;> simp
  rw [hfilter] at hle
  exact hle

end LatticeSystem.Quantum

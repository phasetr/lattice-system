import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLeComplementReIff

/-!
# `(pm¬A).re = max((pmA).re, (pm¬A).re) ↔ |A| ≤ |¬A|` at `N ≥ 1`

Mirror of PR #3147 — the complement predicted-min energy `(pm¬A).re`
equals the orientation-pair max exactly when `¬A` is at least as heavy
as `A`. At `N ≥ 1`:

  `(predicted_min ¬A).re = max((predicted_min A).re, (predicted_min ¬A).re)
   ↔ |A| ≤ |¬A|`.

Direct from `y = max x y ↔ x ≤ y` composed with PR #3070.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pm¬A).re = max iff `|A| ≤ |¬A|`** at `N ≥ 1`. Mirror of PR #3147. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_eq_max_complement_re_iff_cardA_le_cardNotA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
        max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  -- y = max x y ↔ x ≤ y.
  have hymax_iff : (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≤
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
    constructor
    · intro h
      have : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≤
          max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
        le_max_left _ _
      linarith [this, h]
    · intro h
      exact (max_eq_right h).symm
  rw [hymax_iff]
  exact bipartiteToyMinEnergyPredicted_re_le_complement_re_iff_cardA_le_cardNotA
    (Λ := Λ) A N hN

end LatticeSystem.Quantum

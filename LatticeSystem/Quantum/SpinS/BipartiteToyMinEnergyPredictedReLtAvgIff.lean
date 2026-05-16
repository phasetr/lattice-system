import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLtComplementReIff

/-!
# `(pmA).re < avg ↔ |A| < |¬A|` at `N ≥ 1`

Strict version of PR #3135. The canonical predicted-min energy
`(pmA).re` sits strictly below the orientation-pair average exactly
when `A` is strictly lighter than `¬A`. At `N ≥ 1`:

  `(predicted_min A).re < ((predicted_min A).re + (predicted_min ¬A).re) / 2
   ↔ |A| < |¬A|`.

This is `x < (x + y) / 2 ↔ x < y` composed with the existing strict iff.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pmA).re < avg iff `|A| < |¬A|`** at `N ≥ 1`. Strict version of PR #3135. -/
theorem bipartiteToyMinEnergyPredicted_re_lt_avg_complement_re_iff_cardA_lt_cardNotA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re <
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hlt := bipartiteToyMinEnergyPredicted_re_lt_complement_re_iff_cardA_lt_cardNotA
    (Λ := Λ) A N hN
  -- x < (x + y) / 2 ↔ x < y for reals.
  have hmidpoint : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re <
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re <
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hmidpoint]
  exact hlt

end LatticeSystem.Quantum

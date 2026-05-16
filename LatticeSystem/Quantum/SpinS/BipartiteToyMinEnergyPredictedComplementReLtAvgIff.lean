import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLtAvgIff

/-!
# `(pm¬A).re < avg ↔ |¬A| < |A|` at `N ≥ 1`

Mirror of PR #3137 — the complement predicted-min energy `(pm¬A).re`
sits strictly below the orientation-pair average exactly when `¬A` is
strictly lighter than `A`. At `N ≥ 1`:

  `(predicted_min ¬A).re < ((predicted_min A).re + (predicted_min ¬A).re) / 2
   ↔ |¬A| < |A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pm¬A).re < avg iff `|¬A| < |A|`** at `N ≥ 1`. Mirror of PR #3137. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_lt_avg_complement_re_iff_cardNotA_lt_cardA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card <
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
  -- x < (x + y) / 2 ↔ y < x.
  have hmid_iff : (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hmid_iff]
  -- (pm¬A).re < (pmA).re ↔ |¬A| < |A|: apply PR #3067 to ¬A then fold ¬¬A = A.
  have hlt := bipartiteToyMinEnergyPredicted_re_lt_complement_re_iff_cardA_lt_cardNotA
    (Λ := Λ) (fun x : Λ => ! A x) N hN
  have hfunext : (fun x : Λ => ! (! A x)) = A := by
    funext x; cases A x <;> simp
  rw [hfunext] at hlt
  have hfilter : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases A x <;> simp
  rw [hfilter] at hlt
  exact hlt

end LatticeSystem.Quantum

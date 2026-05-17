import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLtComplementReIff

/-!
# `min((pmA).re, (pm¬A).re) < (pm¬A).re ↔ |A| < |¬A|` at `N ≥ 1`

Mirror of PR #3144 — the orientation-pair min sits strictly below the
complement predicted-min energy `(pm¬A).re` exactly when `A` is strictly
lighter than `¬A` (i.e. `(pmA).re < (pm¬A).re`). At `N ≥ 1`:

  `min((predicted_min A).re, (predicted_min ¬A).re) < (predicted_min ¬A).re
   ↔ |A| < |¬A|`.

Direct from `min x y < y ↔ x < y` composed with PR #3067.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min < (pm¬A).re iff `|A| < |¬A|`** at `N ≥ 1`. Mirror of PR #3144. -/
theorem bipartiteToyMinEnergyPredicted_min_lt_complement_re_iff_cardA_lt_cardNotA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hlt := bipartiteToyMinEnergyPredicted_re_lt_complement_re_iff_cardA_lt_cardNotA
    (Λ := Λ) A N hN
  -- min x y < y ↔ x < y.
  rw [min_lt_iff]
  constructor
  · intro h
    rcases h with hxy | hyy
    · exact hlt.mp hxy
    · exact absurd hyy (lt_irrefl _)
  · intro hcard
    exact Or.inl (hlt.mpr hcard)

end LatticeSystem.Quantum

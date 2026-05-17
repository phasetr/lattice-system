import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLtComplementReIff

/-!
# `min((pmA).re, (pm¬A).re) < (pmA).re ↔ |¬A| < |A|` at `N ≥ 1`

The orientation-pair min sits strictly below the canonical
predicted-min energy `(pmA).re` exactly when `¬A` is strictly lighter
than `A` (i.e. `(pm¬A).re < (pmA).re`). At `N ≥ 1`:

  `min((predicted_min A).re, (predicted_min ¬A).re) < (predicted_min A).re
   ↔ |¬A| < |A|`.

Direct from `min x y < x ↔ y < x` composed with PR #3067 applied to `¬A`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min < (pmA).re iff `|¬A| < |A|`** at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_min_lt_re_complement_re_iff_cardNotA_lt_cardA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card <
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
  -- min x y < x ↔ y < x.
  rw [min_lt_iff]
  constructor
  · intro h
    rcases h with hxx | hyx
    · exact absurd hxx (lt_irrefl _)
    · -- (pm¬A).re < (pmA).re ↔ |¬A| < |A|: apply PR #3067 to ¬A, then fold.
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
      exact hlt.mp hyx
  · intro hcard
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
    exact Or.inr (hlt.mpr hcard)

end LatticeSystem.Quantum

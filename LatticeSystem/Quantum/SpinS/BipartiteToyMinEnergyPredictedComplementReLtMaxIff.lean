import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLtComplementReIff

/-!
# `(pm¬A).re < max((pmA).re, (pm¬A).re) ↔ |¬A| < |A|` at `N ≥ 1`

Mirror of PR #3143 — the complement predicted-min energy `(pm¬A).re`
sits strictly below the orientation-pair max exactly when `¬A` is
strictly lighter than `A`. At `N ≥ 1`:

  `(predicted_min ¬A).re < max((predicted_min A).re, (predicted_min ¬A).re)
   ↔ |¬A| < |A|`.

Direct from `y < max x y ↔ y < x` composed with PR #3067 applied to `¬A`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pm¬A).re < max iff `|¬A| < |A|`** at `N ≥ 1`. Mirror of PR #3143. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_lt_max_complement_re_iff_cardNotA_lt_cardA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card <
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
  -- y < max x y ↔ y < x.
  rw [lt_max_iff]
  constructor
  · intro h
    rcases h with hyx | hyy
    · -- (pm¬A).re < (pmA).re ↔ |¬A| < |A|: apply PR #3067 to ¬A then fold.
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
    · exact absurd hyy (lt_irrefl _)
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
    exact Or.inl (hlt.mpr hcard)

end LatticeSystem.Quantum

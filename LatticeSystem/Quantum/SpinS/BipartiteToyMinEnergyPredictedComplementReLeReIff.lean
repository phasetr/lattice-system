import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLeComplementReIff

/-!
# `(pm¬A).re ≤ (pmA).re ↔ |¬A| ≤ |A|` at `N ≥ 1`

Mirror of PR #3069. At `N ≥ 1`:

  `(predicted_min ¬A).re ≤ (predicted_min A).re ↔ |¬A| ≤ |A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pm¬A).re ≤ (pmA).re iff `|¬A| ≤ |A|`** at `N ≥ 1`. Mirror of PR #3069. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_le_re_iff_cardNotA_le_cardA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
        (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
  have h := bipartiteToyMinEnergyPredicted_re_le_complement_re_iff_cardA_le_cardNotA
    (Λ := Λ) (fun x => ! A x) N hN
  have hfun_eq : (fun x : Λ => ! ((fun y => ! A y) x)) = A := by funext x; simp
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfun_eq] at h
  rw [hfilter_eq] at h
  exact h

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLeAvgIff

/-!
# `(pm¬A).re ≤ avg ↔ |¬A| ≤ |A|` at `N ≥ 1`

Mirror of PR #3135 — the complement predicted-min energy `(pm¬A).re`
sits at or below the orientation-pair average exactly when `¬A` is the
lighter sublattice. At `N ≥ 1`:

  `(predicted_min ¬A).re ≤ ((predicted_min A).re + (predicted_min ¬A).re) / 2
   ↔ |¬A| ≤ |A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pm¬A).re ≤ avg iff `|¬A| ≤ |A|`** at `N ≥ 1`. Mirror of PR #3135. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_le_avg_complement_re_iff_cardNotA_le_cardA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
  -- Apply PR #3135 to ¬A; the symmetric avg form makes (pm¬¬A) collapse.
  have hmid_iff : (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
        (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hmid_iff]
  -- (pm¬A).re ≤ (pmA).re ↔ |¬A| ≤ |A|: apply PR #3070 to ¬A.
  have hle := bipartiteToyMinEnergyPredicted_re_le_complement_re_iff_cardA_le_cardNotA
    (Λ := Λ) (fun x : Λ => ! A x) N hN
  -- Goal LHS pm(¬A) ≤ pm(¬¬A) iff card{¬A} ≤ card{¬¬A}.
  -- But we want pm(¬A) ≤ pm(A) iff |¬A| ≤ |A|. So fold ¬¬A back to A.
  have hfunext : (fun x : Λ => ! (! A x)) = A := by
    funext x; cases A x <;> simp
  rw [hfunext] at hle
  -- hle : (pm¬A).re ≤ (pmA).re ↔ |¬A| ≤ |A|. (filter on `¬¬A` becomes filter on `A`.)
  have hfilter : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases A x <;> simp
  rw [hfilter] at hle
  exact hle

end LatticeSystem.Quantum

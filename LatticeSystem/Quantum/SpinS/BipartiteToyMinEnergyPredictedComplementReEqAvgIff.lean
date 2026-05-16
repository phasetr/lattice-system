import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReEqAvgIff

/-!
# `(pm¬A).re = avg ↔ |¬A| = |A|` at `N ≥ 1`

Mirror of PR #3139 — the complement predicted-min energy `(pm¬A).re`
equals the orientation-pair average exactly at balanced. At `N ≥ 1`:

  `(predicted_min ¬A).re = ((predicted_min A).re + (predicted_min ¬A).re) / 2
   ↔ |¬A| = |A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pm¬A).re = avg iff `|¬A| = |A|`** at `N ≥ 1`. Mirror of PR #3139. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_eq_avg_complement_re_iff_balanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
  have hbal := bipartiteToyMinEnergyPredicted_re_eq_complement_re_iff_balanced
    (Λ := Λ) A N hN
  -- y = (x + y) / 2 ↔ y = x.
  have hmid_iff : (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
        (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hmid_iff]
  constructor
  · intro h
    exact (hbal.mp h.symm).symm
  · intro h
    exact (hbal.mpr h.symm).symm

end LatticeSystem.Quantum

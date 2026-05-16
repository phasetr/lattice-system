import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# `avg ≤ (predictedSymm A).re` unconditionally

PR #3001: `max((pmA).re, (pm¬A).re) = (predictedSymm A).re`.

The arithmetic mean of any two reals is at most their max:

  `((predicted_min A).re + (predicted_min ¬A).re) / 2 ≤ (predictedSymm A).re`

unconditionally. Weak version of PR #3034 (which gives the exact
difference `||A| − |¬A||·N/2`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg ≤ predictedSymm** unconditional: weak version of PR #3034. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_le_predictedSymm_re
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ≤
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
  rw [← bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  -- (x + y)/2 ≤ max x y for any reals.
  have hmax_l : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≤
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
    le_max_left _ _
  have hmax_r : (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
    le_max_right _ _
  linarith

end LatticeSystem.Quantum

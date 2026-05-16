import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmReNegIff
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# `max((pmA).re, (pm¬A).re) < 0 ↔ |A| ≥ 1 ∧ |¬A| ≥ 1 ∧ N ≥ 1`

PR #3082: `predictedSymm.re < 0 ↔ non-degenerate`.
PR #3001: `max = predictedSymm`.

Combining:

  `max((predicted_min A).re, (predicted_min ¬A).re) < 0
   ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **max iff strict negativity ↔ non-degenerate**: equivalent to
PR #3082 via PR #3001. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_neg_iff_nondegenerate
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re < 0 ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
        0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
        0 < N := by
  rw [bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  exact bipartiteToyMinEnergyPredictedSymm_re_neg_iff_nondegenerate (Λ := Λ) A N

end LatticeSystem.Quantum

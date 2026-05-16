import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe

/-!
# `(predictedSymm A).re − min(...) = ||A| − |¬A||·N`

PR #3001: `max((predicted_min A).re, (predicted_min ¬A).re) = (predictedSymm A).re`.
PR #3012: `max − min = ||A| − |¬A||·N`.

Combining gives directly:

  `(predictedSymm A).re − min((predicted_min A).re, (predicted_min ¬A).re)
   = ||A| − |¬A||·N`

unconditionally.

This packages the physical interpretation: the symmetric Tasaki §2.5
Theorem 2.3 prediction (`predictedSymm`) sits exactly `||A| − |¬A||·N`
above the "wrong-orientation" prediction (the min of the two
orientation-specific predicted min energies).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **predictedSymm sits exactly `||A| − |¬A||·N` above the min**:
direct from PR #3001 (max = predictedSymm) + PR #3012 (max − min spread). -/
theorem bipartiteToyMinEnergyPredictedSymm_re_sub_min_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        (N : ℝ) := by
  rw [← bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  exact bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq A N

end LatticeSystem.Quantum

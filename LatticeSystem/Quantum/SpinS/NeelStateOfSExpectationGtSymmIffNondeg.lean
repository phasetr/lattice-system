import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGtMaxIffNondeg
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# `(predictedSymm A).re < ⟨Néel⟩.re ↔ non-degenerate`

PR #3105: `max < ⟨Néel⟩.re ↔ non-degenerate`.
PR #3001: `max = predictedSymm`.

  `(predictedSymm A).re < ⟨Néel⟩.re
   ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`.

Mirror of PR #3105 via max-form. Full strict iff for the Tasaki §2.5
Theorem 2.3 prediction strict inequality.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **predictedSymm.re < ⟨Néel⟩.re iff non-degenerate** unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_predictedSymm_re_iff_nondeg
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re <
        (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
        0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
        0 < N := by
  rw [← bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  exact neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_max_complement_re_iff_nondeg
    (Λ := Λ) A N

end LatticeSystem.Quantum

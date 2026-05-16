import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGePredictedSymm
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# Unconditional `max(...) ≤ ⟨Néel⟩.re`

PR #3099: `(predictedSymm A).re ≤ ⟨Néel⟩.re`.
PR #3001: `max = predictedSymm`.

Combining:

  `max((pmA).re, (pm¬A).re) ≤ ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Unconditional `max(...) ≤ ⟨Néel⟩.re`**: combining PR #3099 +
PR #3001. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_max_complement_re
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  rw [bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  exact neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_predictedSymm_re
    (Λ := Λ) A N

end LatticeSystem.Quantum

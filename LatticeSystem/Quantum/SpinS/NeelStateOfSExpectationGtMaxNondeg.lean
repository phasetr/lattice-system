import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGtPredictedSymmNondeg
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# `max(...) < ⟨Néel⟩.re` at non-degenerate

PR #3100: `predictedSymm.re < ⟨Néel⟩.re` at non-degenerate.
PR #3001: `max = predictedSymm`.

Combining:

  `0 < |A|, 0 < |¬A|, 0 < N → max((pmA).re, (pm¬A).re) < ⟨Néel⟩.re`.

Strict version of PR #3101.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`max(...) < ⟨Néel⟩.re` at non-degenerate**: strict version of PR #3101. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_max_complement_re
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  rw [bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  exact neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_predictedSymm_re
    (Λ := Λ) A N hA hAc hN

end LatticeSystem.Quantum

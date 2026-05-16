import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationEqSymmIffUncond
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# `⟨Néel⟩.re = max(...) ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0` unconditionally

PR #3103: `⟨Néel⟩.re = predictedSymm.re ↔ degenerate`.
PR #3001: `max = predictedSymm`.

  `⟨Néel⟩.re = max((pmA).re, (pm¬A).re)
   ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`.

Mirror of PR #3103 via max-form.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **⟨Néel⟩.re = max(...) iff degenerate** unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_max_complement_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
        max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
        N = 0 := by
  rw [bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  exact neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_predictedSymm_re_iff_uncond
    (Λ := Λ) A N

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGapPosNondegenerate

/-!
# `(predictedSymm A).re < ⟨Néel⟩.re` at non-degenerate

PR (existing) gives strict positivity of the gap `(⟨Néel⟩ −
predictedSymm).re > 0` at non-degenerate. This file packages the
direct strict inequality form:

  `0 < |A|, 0 < |¬A|, 0 < N → (predictedSymm A).re < ⟨Néel⟩.re`.

Strict version of PR #3099. Tasaki §2.5 Theorem 2.3 prediction holds
strictly at non-degenerate.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(predictedSymm A).re < ⟨Néel⟩.re` at non-degenerate**. Strict
version of PR #3099. Direct repackaging of the existing strict-gap
result. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_predictedSymm_re
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re <
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  have hgap_pos :=
    neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm_re_pos_of_nondegenerate
      (Λ := Λ) A N hA hAc hN
  rw [Complex.sub_re] at hgap_pos
  linarith

end LatticeSystem.Quantum

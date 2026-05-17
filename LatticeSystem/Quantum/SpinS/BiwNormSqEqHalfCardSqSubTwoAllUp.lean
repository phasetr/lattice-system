import LatticeSystem.Quantum.SpinS.BiwNormSqEqHalfCardSqAddTwoNeel
import LatticeSystem.Quantum.SpinS.AllAlignedExpectationEqNegNeel

/-!
# `‖biw‖² = (|Λ|·N/2)² − 2 · ⟨Φ_↑⟩.re` unconditionally

Mirror of PR #3221 via PR #3199 (`⟨Φ_↑⟩.re = −⟨Φ_Néel⟩.re`):

  `‖biw‖² = (|Λ|·N/2)² − 2 · ⟨Φ_↑|Ĥ_toy|Φ_↑⟩.re`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖² = (|Λ|·N/2)² − 2·⟨Φ_↑⟩.re`** unconditionally. Mirror of PR #3221. -/
theorem bipartiteImbalanceWeight_norm_sq_eq_half_card_sq_sub_two_all_up_expectation_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 =
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 -
        2 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
              ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
                (allAlignedStateS Λ N (0 : Fin (N + 1))))).re := by
  have h1 := bipartiteImbalanceWeight_norm_sq_eq_half_card_sq_add_two_neel_expectation_re
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_neg_neel_expectation_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

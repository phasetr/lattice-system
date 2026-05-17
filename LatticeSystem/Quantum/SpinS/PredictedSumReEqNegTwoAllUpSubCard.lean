import LatticeSystem.Quantum.SpinS.PredictedReAddAllUpAddHalfCardEqBiwRe
import LatticeSystem.Quantum.SpinS.PredictedComplementReAddAllUpAddHalfCardEqNegBiwRe

/-!
# `(pmA).re + (pm¬A).re = −2·⟨Φ_↑⟩.re − |Λ|·N` unconditionally

Sum of PR #3261 + PR #3262. The biw terms cancel.

  `(pmA).re + (pm¬A).re + 2·⟨Φ_↑|Ĥ_toy|Φ_↑⟩.re + |Λ|·N = 0`

equivalently:

  `(pmA).re + (pm¬A).re = −2·⟨Φ_↑⟩.re − |Λ|·N`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(pmA).re + (pm¬A).re = −2·⟨Φ_↑⟩.re − |Λ|·N`** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_sum_re_eq_neg_two_all_up_sub_card_times_n
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      -(2 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
              ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
                (allAlignedStateS Λ N (0 : Fin (N + 1))))).re) -
        (Fintype.card Λ : ℝ) * (N : ℝ) := by
  have h1 := bipartiteToyMinEnergyPredicted_re_add_all_up_add_half_card_eq_biw_re
    (Λ := Λ) (A := A) (N := N)
  have h2 := bipartiteToyMinEnergyPredicted_complement_re_add_all_up_add_half_card_eq_neg_biw_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

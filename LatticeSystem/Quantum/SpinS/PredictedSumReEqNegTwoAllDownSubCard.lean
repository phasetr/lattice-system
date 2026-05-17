import LatticeSystem.Quantum.SpinS.PredictedSumReEqNegTwoAllUpSubCard
import LatticeSystem.Quantum.SpinS.AllUpEqAllDownExpectation

/-!
# `(pmA).re + (pm¬A).re = −2·⟨Φ_↓⟩.re − |Λ|·N` unconditionally

Mirror of PR #3263 via PR #3202.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(pmA).re + (pm¬A).re = −2·⟨Φ_↓⟩.re − |Λ|·N`** unconditionally. Mirror of PR #3263. -/
theorem bipartiteToyMinEnergyPredicted_sum_re_eq_neg_two_all_down_sub_card_times_n
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      -(2 * (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
              ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
                (allAlignedStateS Λ N (Fin.last N)))).re) -
        (Fintype.card Λ : ℝ) * (N : ℝ) := by
  have h1 := bipartiteToyMinEnergyPredicted_sum_re_eq_neg_two_all_up_sub_card_times_n
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.PredictedSumReEqNegTwoAllUpSubCard
import LatticeSystem.Quantum.SpinS.AllAlignedExpectationEqNegNeel

/-!
# `(pmA).re + (pm¬A).re = 2·⟨Φ_Néel⟩.re − |Λ|·N` unconditionally

Combines PR #3263 + PR #3199 (`⟨Φ_↑⟩.re = −⟨Φ_Néel⟩.re`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(pmA).re + (pm¬A).re = 2·⟨Φ_Néel⟩.re − |Λ|·N`** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_sum_re_eq_two_neel_sub_card_times_n
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      2 * (dotProduct (star (neelStateOfS A N))
              ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
                (neelStateOfS A N))).re -
        (Fintype.card Λ : ℝ) * (N : ℝ) := by
  have h1 := bipartiteToyMinEnergyPredicted_sum_re_eq_neg_two_all_up_sub_card_times_n
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_neg_neel_expectation_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

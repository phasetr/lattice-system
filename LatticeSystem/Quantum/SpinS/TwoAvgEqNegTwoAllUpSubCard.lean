import LatticeSystem.Quantum.SpinS.PredictedSumReEqNegTwoAllUpSubCard

/-!
# `2·avg = −2·⟨Φ_↑⟩.re − |Λ|·N` unconditionally

Direct from PR #3263 since `2·avg = (pmA + pm¬A).re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`2·avg = −2·⟨Φ_↑⟩.re − |Λ|·N`** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_two_avg_complement_re_eq_neg_two_all_up_sub_card_times_n
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    2 * (((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2) =
      -(2 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
              ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
                (allAlignedStateS Λ N (0 : Fin (N + 1))))).re) -
        (Fintype.card Λ : ℝ) * (N : ℝ) := by
  have h := bipartiteToyMinEnergyPredicted_sum_re_eq_neg_two_all_up_sub_card_times_n
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

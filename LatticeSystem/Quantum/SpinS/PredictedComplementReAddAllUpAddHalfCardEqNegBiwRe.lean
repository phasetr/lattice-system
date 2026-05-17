import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubComplementEqHalfCardAddBiwRe
import LatticeSystem.Quantum.SpinS.AllAlignedExpectationEqNegNeel

/-!
# `(pm¬A).re + ⟨Φ_↑⟩.re + |Λ|·N/2 = −biw.re` unconditionally

Mirror of PR #3261. Combines PR #3172 + PR #3199.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(pm¬A).re + ⟨Φ_↑⟩.re + |Λ|·N/2 = −biw.re`** unconditionally. Mirror of PR #3261. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_add_all_up_add_half_card_eq_neg_biw_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re +
        (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re +
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 =
      -(bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  have h1 := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_complement_predicted_re_eq_half_card_add_biw_re
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_neg_neel_expectation_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

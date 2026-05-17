import LatticeSystem.Quantum.SpinS.EightAllUpEqCardSqSubTwoBiwNormSq
import LatticeSystem.Quantum.SpinS.AllUpEqAllDownExpectation

/-!
# `8 · ⟨Φ_↓⟩.re = (|Λ|·N)² − (2·‖biw‖)²` unconditionally

Mirror of PR #3257 via PR #3202.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`8·⟨Φ_↓⟩.re = (|Λ|·N)² − (2·‖biw‖)²`** unconditionally. Mirror of PR #3257. -/
theorem heisenbergToyHamiltonianS_eight_allAligned_last_expectation_re_eq_card_sq_sub_two_biw_norm_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    8 * (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re =
      ((Fintype.card Λ : ℝ) * (N : ℝ)) ^ 2 -
        (2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) ^ 2 := by
  have h1 := heisenbergToyHamiltonianS_eight_allAligned_zero_expectation_re_eq_card_sq_sub_two_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

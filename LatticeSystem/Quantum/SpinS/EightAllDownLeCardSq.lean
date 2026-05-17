import LatticeSystem.Quantum.SpinS.EightAllDownEqCardSqSubTwoBiwNormSq

/-!
# `8 · ⟨Φ_↓⟩.re ≤ (|Λ|·N)²` unconditionally

Mirror of PR #3288. Direct from PR #3259 (`8·⟨Φ_↓⟩.re = (|Λ|·N)² −
(2·‖biw‖)²`) and `0 ≤ (2·‖biw‖)²`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`8·⟨Φ_↓⟩.re ≤ (|Λ|·N)²`** unconditionally. Mirror of PR #3288. -/
theorem heisenbergToyHamiltonianS_eight_allAligned_last_expectation_re_le_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    8 * (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ)) ^ 2 := by
  have h_eq := heisenbergToyHamiltonianS_eight_allAligned_last_expectation_re_eq_card_sq_sub_two_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have h_sq_nn : (0 : ℝ) ≤ (2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) ^ 2 := sq_nonneg _
  linarith

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.EightAllUpEqCardSqSubTwoBiwReSq

/-!
# `(|Λ|·N − 2·biw.re)·(|Λ|·N + 2·biw.re) = 8·⟨Φ_↑⟩.re` unconditionally

Difference-of-squares factorization of PR #3300:

  `(|Λ|·N − 2·biw.re)·(|Λ|·N + 2·biw.re) =
      (|Λ|·N)² − (2·biw.re)² = 8·⟨Φ_↑⟩.re`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(|Λ|·N − 2·biw.re)·(|Λ|·N + 2·biw.re) = 8·⟨Φ_↑⟩.re`** unconditionally. -/
theorem bipartiteImbalanceWeight_card_sub_two_re_mul_add_two_re_eq_eight_all_up
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ((Fintype.card Λ : ℝ) * (N : ℝ) -
          2 * (bipartiteImbalanceWeight (Λ := Λ) A N).re) *
        ((Fintype.card Λ : ℝ) * (N : ℝ) +
          2 * (bipartiteImbalanceWeight (Λ := Λ) A N).re) =
      8 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re := by
  have h := heisenbergToyHamiltonianS_eight_allAligned_zero_expectation_re_eq_card_sq_sub_two_biw_re_sq
    (Λ := Λ) (A := A) (N := N)
  linear_combination -h

end LatticeSystem.Quantum

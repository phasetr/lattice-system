import LatticeSystem.Quantum.SpinS.FourGapEqCardSqSubTwoBiwNormSq
import LatticeSystem.Quantum.SpinS.TwoAllUpExpectationEqVariationalGap

/-!
# `8 · ⟨Φ_↑⟩.re = (|Λ|·N)² − (2·‖biw‖)²` unconditionally

Combines PR #3256 (`4·gap = (|Λ|·N)² − (2·‖biw‖)²`) with PR #3200
(`2·⟨Φ_↑⟩.re = gap.re`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`8·⟨Φ_↑⟩.re = (|Λ|·N)² − (2·‖biw‖)²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_eight_allAligned_zero_expectation_re_eq_card_sq_sub_two_biw_norm_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    8 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re =
      ((Fintype.card Λ : ℝ) * (N : ℝ)) ^ 2 -
        (2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) ^ 2 := by
  have h1 := heisenbergToyHamiltonianS_four_variational_gap_re_eq_card_sq_sub_two_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_two_allAligned_zero_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

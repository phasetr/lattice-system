import LatticeSystem.Quantum.SpinS.TwoAllUpExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwReSq

/-!
# `2·⟨Φ_↑⟩.re = (|Λ|·N/2)² − biw.re²` unconditionally

Combines PR #3200 (`2·⟨Φ_↑⟩.re = gap.re`) + PR #3295
(`gap.re = (|Λ|·N/2)² − biw.re²`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`2·⟨Φ_↑⟩.re = (|Λ|·N/2)² − biw.re²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_two_allAligned_zero_expectation_re_eq_half_card_sq_sub_biw_re_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    2 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re =
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := by
  have h1 := heisenbergToyHamiltonianS_two_allAligned_zero_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_re_sq
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

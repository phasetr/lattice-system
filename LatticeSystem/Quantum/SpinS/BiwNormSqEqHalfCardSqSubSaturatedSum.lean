import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwNormSq
import LatticeSystem.Quantum.SpinS.AllUpAddAllDownExpectationEqVariationalGap

/-!
# `‖biw‖² = (|Λ|·N/2)² − (⟨Φ_↑⟩ + ⟨Φ_↓⟩).re` unconditionally

Combines PR #3196 (`gap = (|Λ|·N/2)² − ‖biw‖²`) with PR #3215
(`(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = gap.re`):

  `‖biw‖² = (|Λ|·N/2)² − (⟨Φ_↑|Ĥ_toy|Φ_↑⟩ + ⟨Φ_↓|Ĥ_toy|Φ_↓⟩).re`

unconditionally. Expresses the imbalance-weight squared norm directly
in terms of the saturated-state sum (without going through the gap).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖² = (|Λ|·N/2)² − saturated_sum`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_sq_eq_half_card_sq_sub_all_up_add_all_down_expectation_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 =
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 -
        (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
              ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
                (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
            dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
              ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
                (allAlignedStateS Λ N (Fin.last N)))).re := by
  have h1 := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

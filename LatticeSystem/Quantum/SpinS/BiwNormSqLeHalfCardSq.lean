import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwNormSq
import LatticeSystem.Quantum.SpinS.VariationalGapReNonneg

/-!
# `‖biw‖² ≤ (|Λ|·N/2)²` unconditionally

The imbalance-weight squared norm is bounded above by `(|Λ|·N/2)²`.
Combines PR #3196 (`gap = (|Λ|·N/2)² − ‖biw‖²`) with PR #3195 (`gap ≥ 0`):

  `‖biw‖² ≤ (|Λ|·N/2)²`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖² ≤ (|Λ|·N/2)²`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_sq_le_half_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 := by
  have h1 := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_variational_gap_re_nonneg
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

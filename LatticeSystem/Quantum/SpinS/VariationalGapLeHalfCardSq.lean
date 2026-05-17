import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwNormSq
import LatticeSystem.Quantum.SpinS.BiwNormSqNonneg

/-!
# `gap.re ≤ (|Λ|·N/2)²` unconditionally

The variational gap is bounded above by the squared half-card.
Combines PR #3196 (`gap = (|Λ|·N/2)² − ‖biw‖²`) with PR #3239
(`0 ≤ ‖biw‖²`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`gap.re ≤ (|Λ|·N/2)²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_variational_gap_re_le_half_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 := by
  have h_eq := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have h_sq := bipartiteImbalanceWeight_norm_sq_nonneg (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum

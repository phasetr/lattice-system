import LatticeSystem.Quantum.SpinS.VariationalGapLeHalfCardSq

/-!
# `4 · gap.re ≤ (|Λ|·N)²` unconditionally

Doubled form of PR #3278.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`4·gap ≤ (|Λ|·N)²`** unconditionally. Doubled form of PR #3278. -/
theorem heisenbergToyHamiltonianS_four_variational_gap_re_le_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    4 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ)) ^ 2 := by
  have h := heisenbergToyHamiltonianS_variational_gap_re_le_half_card_sq
    (Λ := Λ) (A := A) (N := N)
  -- 4·gap ≤ 4·(|Λ|·N/2)² = (|Λ|·N)².
  linarith [h, sq_nonneg ((Fintype.card Λ : ℝ) * (N : ℝ))]

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwNormSq

/-!
# `4 · variational_gap = (|Λ|·N)² − (2·‖biw‖)²` unconditionally

Doubled form of PR #3196. From `gap = (|Λ|·N/2)² − ‖biw‖²` multiply
both sides by 4:

  `4 · (⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re = (|Λ|·N)² − (2·‖biw‖)²`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`4·gap = (|Λ|·N)² − (2·‖biw‖)²`** unconditionally. Doubled form of PR #3196. -/
theorem heisenbergToyHamiltonianS_four_variational_gap_re_eq_card_sq_sub_two_biw_norm_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    4 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re =
      ((Fintype.card Λ : ℝ) * (N : ℝ)) ^ 2 -
        (2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) ^ 2 := by
  have h := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  linarith [sq_nonneg ((Fintype.card Λ : ℝ) * (N : ℝ)),
    sq_nonneg ‖bipartiteImbalanceWeight (Λ := Λ) A N‖]

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwNormSq
import LatticeSystem.Quantum.SpinS.NegTwoNeelExpectationEqVariationalGap

/-!
# `‖biw‖² = (|Λ|·N/2)² + 2 · ⟨Φ_Néel⟩.re` unconditionally

Combines PR #3196 (`gap = (|Λ|·N/2)² − ‖biw‖²`) with PR #3201
(`−2·⟨Φ_Néel⟩.re = gap.re`):

  `‖biw‖² = (|Λ|·N/2)² + 2 · ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`

unconditionally.

Concretely: `‖biw‖² = ||A|−|¬A||²·N²/4`, `(|Λ|·N/2)² = |Λ|²·N²/4`,
`Néel.re = −|A|·|¬A|·N²/2`. Then:
  `(|Λ|·N/2)² + 2·Néel.re = |Λ|²·N²/4 − |A|·|¬A|·N²
   = (|Λ|² − 4·|A|·|¬A|)·N²/4
   = ((|A|+|¬A|)² − 4·|A|·|¬A|)·N²/4
   = (|A|−|¬A|)²·N²/4 = ‖biw‖²`. ✓

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖² = (|Λ|·N/2)² + 2·⟨Φ_Néel⟩.re`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_sq_eq_half_card_sq_add_two_neel_expectation_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 =
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 +
        2 * (dotProduct (star (neelStateOfS A N))
              ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
                (neelStateOfS A N))).re := by
  have h1 := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_neg_two_neel_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum

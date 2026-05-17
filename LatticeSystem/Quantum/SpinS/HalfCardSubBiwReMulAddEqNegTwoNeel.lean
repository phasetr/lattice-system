import LatticeSystem.Quantum.SpinS.NegTwoNeelEqHalfCardSqSubBiwReSq

/-!
# `(|Λ|·N/2 − biw.re)·(|Λ|·N/2 + biw.re) = −2·⟨Φ_Néel⟩.re` unconditionally

Difference-of-squares factorization of PR #3299.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(|Λ|·N/2 − biw.re)·(|Λ|·N/2 + biw.re) = −2·⟨Φ_Néel⟩.re`** unconditionally. -/
theorem bipartiteImbalanceWeight_half_card_sub_re_mul_add_re_eq_neg_two_neel
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 -
          (bipartiteImbalanceWeight (Λ := Λ) A N).re) *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 +
          (bipartiteImbalanceWeight (Λ := Λ) A N).re) =
      -(2 * (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re) := by
  have h := heisenbergToyHamiltonianS_neg_two_neel_expectation_re_eq_half_card_sq_sub_biw_re_sq
    (Λ := Λ) (A := A) (N := N)
  linear_combination -h

end LatticeSystem.Quantum

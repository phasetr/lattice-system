import LatticeSystem.Quantum.SpinS.BiwReSqEqNormSq

/-!
# `(|Λ|·N/2 − |biw.re|)·(|Λ|·N/2 + |biw.re|) = (|Λ|·N/2)² − biw.re²` unconditionally

Direct algebraic identity using `|x|² = x²`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`(|Λ|·N/2 − |biw.re|)·(|Λ|·N/2 + |biw.re|) = (|Λ|·N/2)² − biw.re²`** unconditionally. -/
theorem bipartiteImbalanceWeight_half_card_sub_abs_re_mul_add_abs_re_eq_half_card_sq_sub_re_sq
    (A : Λ → Bool) (N : ℕ) :
    ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 -
          |(bipartiteImbalanceWeight (Λ := Λ) A N).re|) *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 +
          |(bipartiteImbalanceWeight (Λ := Λ) A N).re|) =
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := by
  have h_abs_sq : |(bipartiteImbalanceWeight (Λ := Λ) A N).re| ^ 2 =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := sq_abs _
  nlinarith [h_abs_sq]

end LatticeSystem.Quantum

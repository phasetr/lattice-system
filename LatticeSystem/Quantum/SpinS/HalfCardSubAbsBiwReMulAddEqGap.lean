import LatticeSystem.Quantum.SpinS.HalfCardSubBiwReMulAddEqGap

/-!
# `(|Λ|·N/2 − |biw.re|)·(|Λ|·N/2 + |biw.re|) = gap.re` unconditionally

Absolute-value variant of PR #3305. Since `(a − b)(a + b) = (a − |b|)(a + |b|)`
when `|b|² = b²`, this rewrites PR #3305's factored form with `|biw.re|`
in place of `biw.re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(|Λ|·N/2 − |biw.re|)·(|Λ|·N/2 + |biw.re|) = gap.re`** unconditionally. -/
theorem bipartiteImbalanceWeight_half_card_sub_abs_re_mul_add_abs_re_eq_gap
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 -
          |(bipartiteImbalanceWeight (Λ := Λ) A N).re|) *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 +
          |(bipartiteImbalanceWeight (Λ := Λ) A N).re|) =
      (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re := by
  have h := bipartiteImbalanceWeight_half_card_sub_re_mul_add_re_eq_gap
    (Λ := Λ) (A := A) (N := N)
  have h_abs_sq : |(bipartiteImbalanceWeight (Λ := Λ) A N).re| ^ 2 =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := sq_abs _
  nlinarith [h, h_abs_sq]

end LatticeSystem.Quantum

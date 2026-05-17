import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwNormSq
import LatticeSystem.Quantum.SpinS.VariationalGapReEqZeroIff

/-!
# iff: `‖biw‖² = (|Λ|·N/2)² ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`

The squared imbalance-weight norm equals its squared upper bound
exactly at degenerate cases. Combines PR #3196 + PR #3194.

  `‖biw‖² = (|Λ|·N/2)² ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖² = (|Λ|·N/2)² iff degenerate`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_sq_eq_half_card_sq_iff
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 =
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
      N = 0 := by
  have hgap_form := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have hgap_zero := heisenbergToyHamiltonianS_variational_gap_re_eq_zero_iff
    (Λ := Λ) (A := A) (N := N)
  constructor
  · intro heq
    have hgap_eq : (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re = 0 := by linarith
    exact hgap_zero.mp hgap_eq
  · intro hor
    have hgap_eq : (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re = 0 := hgap_zero.mpr hor
    linarith

end LatticeSystem.Quantum

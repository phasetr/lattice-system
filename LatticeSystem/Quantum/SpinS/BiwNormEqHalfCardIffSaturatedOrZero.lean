import LatticeSystem.Quantum.SpinS.BiwNormSqLeHalfCardSq
import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwNormSq
import LatticeSystem.Quantum.SpinS.VariationalGapReEqZeroIff

/-!
# iff: `‖biw‖ = |Λ|·N/2 ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`

The imbalance-weight norm equals its upper bound exactly at saturated
edges or `N = 0`.

  `‖biw‖ = |Λ|·N/2 ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`

unconditionally. Combines PR #3196 (`gap = (|Λ|·N/2)² − ‖biw‖²`) with
PR #3194 (`gap = 0 ↔ degenerate`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖ = |Λ|·N/2 iff some factor is 0`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_eq_half_card_iff_saturated_or_n_zero
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = (Fintype.card Λ : ℝ) * (N : ℝ) / 2 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
      N = 0 := by
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  have hhalf_nn : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    have hΛ : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    positivity
  -- ‖biw‖ = |Λ|·N/2 ↔ ‖biw‖² = (|Λ|·N/2)² (since both non-negative)
  -- ↔ gap = 0 (via PR #3196) ↔ some factor 0 (via PR #3194).
  have hgap_form := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have hgap_zero := heisenbergToyHamiltonianS_variational_gap_re_eq_zero_iff
    (Λ := Λ) (A := A) (N := N)
  constructor
  · intro heq
    -- ‖biw‖ = |Λ|·N/2 → ‖biw‖² = (|Λ|·N/2)² → gap = 0.
    have hsq_eq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 =
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 := by rw [heq]
    have hgap_eq : (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re = 0 := by linarith
    exact hgap_zero.mp hgap_eq
  · intro hor
    -- some factor = 0 → gap = 0 → ‖biw‖² = (|Λ|·N/2)² → ‖biw‖ = |Λ|·N/2.
    have hgap_eq : (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re = 0 := hgap_zero.mpr hor
    have hsq_eq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 =
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 := by linarith
    -- Both non-negative, equal squares → equal.
    nlinarith [sq_nonneg (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2),
      sq_nonneg (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2)]

end LatticeSystem.Quantum

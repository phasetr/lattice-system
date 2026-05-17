import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwNormSq
import LatticeSystem.Quantum.SpinS.VariationalGapRePosIff

/-!
# iff: `‖biw‖² < (|Λ|·N/2)² ↔ nondeg`

The squared imbalance-weight norm is strictly less than the squared
half-card exactly at non-degenerate.

  `‖biw‖² < (|Λ|·N/2)² ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`.

Combines PR #3196 (`gap = (|Λ|·N/2)² − ‖biw‖²`) + PR #3193 (gap pos iff).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖² < (|Λ|·N/2)² iff nondeg`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_sq_lt_half_card_sq_iff_nondeg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 <
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  have hgap_form := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have hgap_pos_iff := heisenbergToyHamiltonianS_variational_gap_re_pos_iff_nondeg
    (Λ := Λ) (A := A) (N := N)
  constructor
  · intro hlt
    have hgap_pos : 0 < (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re := by linarith
    exact hgap_pos_iff.mp hgap_pos
  · intro hor
    have hgap_pos : 0 < (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re := hgap_pos_iff.mpr hor
    linarith

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.BiwNormEqAbsRe
import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwNormSq

/-!
# `gap.re = (|Λ|·N/2)² − biw.re²` unconditionally

Real-axis variant of PR #3196 using PR #3294 (`‖biw‖ = |biw.re|`):

  `(⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re = (|Λ|·N/2)² − biw.re²`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`gap.re = (|Λ|·N/2)² − biw.re²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_re_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re =
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := by
  have h_norm := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have h_eq := bipartiteImbalanceWeight_norm_eq_abs_re (Λ := Λ) (A := A) (N := N)
  rw [h_norm, h_eq, sq_abs]

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.BiwNormEqAbsRe
import LatticeSystem.Quantum.SpinS.FourSaturatedSumEqCardSqSubTwoBiwNormSq

/-!
# `4·(⟨Φ_↑⟩+⟨Φ_↓⟩).re = (|Λ|·N)² − (2·biw.re)²` unconditionally

Real-axis variant of PR #3260 using PR #3294 (`‖biw‖ = |biw.re|`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`4·(⟨Φ_↑⟩+⟨Φ_↓⟩).re = (|Λ|·N)² − (2·biw.re)²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_four_allAligned_zero_add_last_expectation_re_eq_card_sq_sub_two_biw_re_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    4 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
          dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re =
      ((Fintype.card Λ : ℝ) * (N : ℝ)) ^ 2 -
        (2 * (bipartiteImbalanceWeight (Λ := Λ) A N).re) ^ 2 := by
  have h_norm := heisenbergToyHamiltonianS_four_allAligned_zero_add_last_expectation_re_eq_card_sq_sub_two_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have h_eq := bipartiteImbalanceWeight_norm_eq_abs_re (Λ := Λ) (A := A) (N := N)
  rw [h_norm, h_eq]
  ring_nf
  rw [sq_abs]

end LatticeSystem.Quantum

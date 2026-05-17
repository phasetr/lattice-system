import LatticeSystem.Quantum.SpinS.NegEightNeelEqCardSqSubTwoBiwNormSq

/-!
# `−8 · ⟨Φ_Néel⟩.re ≤ (|Λ|·N)²` unconditionally

Direct from PR #3258 (`−8·⟨Φ_Néel⟩.re = (|Λ|·N)² − (2·‖biw‖)²`) and
`0 ≤ (2·‖biw‖)²`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`−8·⟨Φ_Néel⟩.re ≤ (|Λ|·N)²`** unconditionally. Direct from PR #3258. -/
theorem heisenbergToyHamiltonianS_neg_eight_neel_expectation_re_le_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    -(8 * (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re) ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ)) ^ 2 := by
  have h_eq := heisenbergToyHamiltonianS_neg_eight_neel_expectation_re_eq_card_sq_sub_two_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  have h_sq_nn : (0 : ℝ) ≤ (2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) ^ 2 := sq_nonneg _
  linarith

end LatticeSystem.Quantum

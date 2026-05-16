import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgComplementReNegIff
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgLeZero

/-!
# `avg = 0 ↔ |Λ| = 0 ∨ N = 0`

PR #3080: `avg < 0 ↔ |Λ| ≥ 1 ∧ N ≥ 1`.
PR #3042: `avg ≤ 0` unconditional.

Contrapositive of #3080 + non-positivity:

  `((predicted_min A).re + (predicted_min ¬A).re) / 2 = 0
   ↔ |Λ| = 0 ∨ N = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg = 0 iff `|Λ| = 0 ∨ N = 0`** unconditionally. Contrapositive
of PR #3080 + PR #3042. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_eq_zero_iff_card_zero
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 = 0 ↔
      Fintype.card Λ = 0 ∨ N = 0 := by
  have hlt_iff := bipartiteToyMinEnergyPredicted_avg_complement_re_neg_iff_card_pos
    (Λ := Λ) A N
  have hnonpos := bipartiteToyMinEnergyPredicted_avg_complement_re_le_zero
    (Λ := Λ) A N
  constructor
  · intro heq
    by_contra hne
    push Not at hne
    obtain ⟨hΛ_ne, hN_ne⟩ := hne
    have hΛ : 0 < Fintype.card Λ := Nat.pos_of_ne_zero hΛ_ne
    have hN : 0 < N := Nat.pos_of_ne_zero hN_ne
    have hlt := hlt_iff.mpr ⟨hΛ, hN⟩
    linarith
  · intro hor
    have hnotlt : ¬ ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 < 0 := by
      intro hlt
      obtain ⟨hΛ, hN⟩ := hlt_iff.mp hlt
      rcases hor with h | h
      · exact (Nat.pos_iff_ne_zero.mp hΛ) h
      · exact (Nat.pos_iff_ne_zero.mp hN) h
    linarith

end LatticeSystem.Quantum

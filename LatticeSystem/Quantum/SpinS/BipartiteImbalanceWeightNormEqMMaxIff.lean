import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormSaturated
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLtMMaxNondegenerate

/-!
# Iff: `‖biw‖ = m_max ↔ saturated edge` at `N ≥ 1`

PR #2851/#2852 (`bipartiteImbalanceWeight_norm_eq_mMax_of_cardNotA_zero`
and `_of_cardA_zero`) give the backward direction: saturated implies
`‖biw‖ = m_max`.

PR #2877 (`bipartiteImbalanceWeight_norm_lt_mMax_of_nondegenerate`)
gives the strict `‖biw‖ < m_max` at non-degenerate. Taking
contrapositive, at `N ≥ 1`, `‖biw‖ ≥ m_max → saturated`. Combined
with the unconditional `‖biw‖ ≤ m_max` (PR #2874):

  `‖biw‖ = m_max ↔ |A| = 0 ∨ |¬A| = 0`   at `N ≥ 1`.

The imbalance norm hits its maximum exactly at saturated edges.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff: `‖biw‖ = m_max ↔ saturated edge`** at `N ≥ 1`. -/
theorem bipartiteImbalanceWeight_norm_eq_mMax_iff_saturated
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  constructor
  · intro heq
    by_contra hne
    push Not at hne
    obtain ⟨hA_ne, hAc_ne⟩ := hne
    have hA_pos : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card :=
      Nat.pos_of_ne_zero hA_ne
    have hAc_pos : 0 <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
      Nat.pos_of_ne_zero hAc_ne
    have hlt :=
      bipartiteImbalanceWeight_norm_lt_mMax_of_nondegenerate A N hA_pos hAc_pos hN
    linarith
  · intro h
    rcases h with hA | hAc
    · exact bipartiteImbalanceWeight_norm_eq_mMax_of_cardA_zero A N hA
    · exact bipartiteImbalanceWeight_norm_eq_mMax_of_cardNotA_zero A N hAc

end LatticeSystem.Quantum

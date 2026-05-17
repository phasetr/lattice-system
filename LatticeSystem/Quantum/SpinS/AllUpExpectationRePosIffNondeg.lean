import LatticeSystem.Quantum.SpinS.AllUpExpectationReNonneg
import LatticeSystem.Quantum.SpinS.AllUpExpectationReEqZeroIff

/-!
# iff: `0 < ⟨Φ_↑⟩.re ↔ nondeg`

The all-up state's toy-Hamiltonian expectation is strictly positive
exactly at non-degenerate. Combines PR #3240 (`0 ≤ ⟨Φ_↑⟩.re`) +
PR #3243 (`⟨Φ_↑⟩.re = 0 ↔ degenerate`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 < ⟨Φ_↑⟩.re iff nondeg`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_expectation_re_pos_iff_nondeg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 < (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  have hnn := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_nonneg
    (Λ := Λ) (A := A) (N := N)
  have heq_zero := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_zero_iff
    (Λ := Λ) (A := A) (N := N)
  constructor
  · intro hpos
    have hne : (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re ≠ 0 := ne_of_gt hpos
    have hnot_deg : ¬ ((Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨ N = 0) :=
      fun h => hne (heq_zero.mpr h)
    push Not at hnot_deg
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.pos_of_ne_zero hnot_deg.1
    · exact Nat.pos_of_ne_zero hnot_deg.2.1
    · exact Nat.pos_of_ne_zero hnot_deg.2.2
  · intro ⟨hA, hNotA, hN⟩
    have hnot_deg : ¬ ((Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨ N = 0) := by
      intro hor
      rcases hor with hA0 | hNotA0 | hN0
      · exact absurd hA (by rw [hA0]; exact lt_irrefl _)
      · exact absurd hNotA (by rw [hNotA0]; exact lt_irrefl _)
      · exact absurd hN (by rw [hN0]; exact lt_irrefl _)
    have hne : (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re ≠ 0 :=
      fun heq => hnot_deg (heq_zero.mp heq)
    exact lt_of_le_of_ne hnn (Ne.symm hne)

end LatticeSystem.Quantum

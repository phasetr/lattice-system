import LatticeSystem.Quantum.SpinS.AllAlignedAddNeelExpectationEqZero
import LatticeSystem.Quantum.SpinS.AllUpExpectationReEqZeroIff

/-!
# iff: `⟨Φ_Néel⟩.re = 0 ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`

The Néel state's toy-Hamiltonian expectation vanishes exactly at
degenerate. Combines PR #3198 (`⟨Φ_↑⟩ + ⟨Φ_Néel⟩ = 0`) + PR #3243.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Φ_Néel⟩.re = 0 iff degenerate`** unconditionally. -/
theorem heisenbergToyHamiltonianS_neel_expectation_re_eq_zero_iff
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
      N = 0 := by
  have h_sum := heisenbergToyHamiltonianS_allAligned_zero_add_neel_expectation_re_eq_zero
    (Λ := Λ) (A := A) (N := N)
  rw [Complex.add_re] at h_sum
  have h_up_zero := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_zero_iff
    (Λ := Λ) (A := A) (N := N)
  constructor
  · intro heq
    have h_up_eq : (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re = 0 := by linarith
    exact h_up_zero.mp h_up_eq
  · intro hor
    have h_up_eq : (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re = 0 := h_up_zero.mpr hor
    linarith

end LatticeSystem.Quantum

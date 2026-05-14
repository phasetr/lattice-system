import LatticeSystem.Quantum.SpinS.HeisenbergToyHamiltonianZeroSaturated

/-!
# Toy Hamiltonian vanishes at the opposite saturated case `|A| = 0`

Mirror of PR #2806: when `|A| = 0`, the toy Hamiltonian
`heisenbergToyHamiltonianS A N` is the zero operator. Directly
from `heisenbergToyHamiltonianS = 2 • sublatticeSpinSDot N A (¬A)`
(PR #1055) and the sublattice spin operators vanishing for the
empty `A` sublattice (PR #2784).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Toy Hamiltonian vanishes when `|A| = 0`**:
`heisenbergToyHamiltonianS A N = 0`. Mirror of PR #2806 for the
opposite orientation. -/
theorem heisenbergToyHamiltonianS_eq_zero_of_cardA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    heisenbergToyHamiltonianS (Λ := Λ) A N = 0 := by
  rw [heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot]
  unfold sublatticeSpinSDot
  rw [sublatticeSpinSOp1_eq_zero_of_card_zero A h,
      sublatticeSpinSOp2_eq_zero_of_card_zero A h,
      sublatticeSpinSOp3_eq_zero_of_card_zero A h]
  simp

end LatticeSystem.Quantum

import LatticeSystem.Quantum.SpinS.SublatticeEqTotalOfCardZero
import LatticeSystem.Quantum.SpinS.ToyHamiltonianCasimir
import LatticeSystem.Quantum.SpinS.SublatticeSpinDot

/-!
# Toy Hamiltonian vanishes at the saturated edge case

When `|¬A| = 0`, the toy Hamiltonian
`heisenbergToyHamiltonianS A N = 2 • sublatticeSpinSDot N A (¬A)`
(PR #1055) involves the cross-sublattice dot product
`sublatticeSpinSDot N A (¬A) = Σ_α (Ŝ_A^α)(Ŝ_¬A^α)`. Since
`Ŝ_¬A^(α) = 0` at the saturated case (PR #2784), each summand
vanishes, so the entire cross-sublattice spin dot is zero and
hence the toy Hamiltonian itself is zero:

  `heisenbergToyHamiltonianS A N = 0`  when `|¬A| = 0`.

Physical interpretation: at the saturated bipartite case there
are no cross-sublattice bonds (¬A is empty), so the bipartite toy
Hamiltonian has no terms.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Toy Hamiltonian vanishes at the saturated case**: when
`|¬A| = 0`, `heisenbergToyHamiltonianS A N = 0`. -/
theorem heisenbergToyHamiltonianS_eq_zero_of_cardNotA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    heisenbergToyHamiltonianS (Λ := Λ) A N = 0 := by
  rw [heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot]
  -- Now: 2 • sublatticeSpinSDot N A (¬A) = 0.
  unfold sublatticeSpinSDot
  rw [sublatticeSpinSOp1_eq_zero_of_card_zero (fun x => ! A x) h,
      sublatticeSpinSOp2_eq_zero_of_card_zero (fun x => ! A x) h,
      sublatticeSpinSOp3_eq_zero_of_card_zero (fun x => ! A x) h]
  simp

end LatticeSystem.Quantum

/-
The ring Heisenberg Hamiltonian as a sum over nearest-neighbor bonds
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 17).

The directed nearest-neighbor coupling `ringCoupling (2n)` is `1` exactly on successor pairs
`(x, x+1 mod 2n)`, so the double-sum Heisenberg Hamiltonian collapses to a single sum over bonds:
`heisenbergHamiltonianS (ringCoupling (2n)) N = ∑_x Ŝ_x · Ŝ_{x+1}`.  This bond form is the starting
point for splitting the ring Hamiltonian into its left, right, and crossing bonds.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionLeftHamiltonian

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- The cyclic successor on the ring `Fin (2n)`: `x ↦ x + 1 (mod 2n)`. -/
def ringSucc (n : ℕ) (x : Fin (2 * n)) : Fin (2 * n) :=
  ⟨(x.val + 1) % (2 * n), Nat.mod_lt _ (by have := x.isLt; omega)⟩

/-- The underlying value of the cyclic successor. -/
@[simp] theorem ringSucc_val (x : Fin (2 * n)) :
    (ringSucc n x).val = (x.val + 1) % (2 * n) := rfl

/-- **The ring Heisenberg Hamiltonian as a bond sum.**  The directed nearest-neighbor coupling
collapses the double sum to a single sum over the bonds `(x, x+1)`. -/
theorem heisenbergHamiltonianS_ringCoupling_eq_bondSum (n N : ℕ) :
    heisenbergHamiltonianS (ringCoupling (2 * n)) N
      = ∑ x : Fin (2 * n), spinSDot x (ringSucc n x) N := by
  rw [heisenbergHamiltonianS_def]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (ringSucc n x)]
  · rw [ringCoupling, if_pos (ringSucc_val x), one_smul]
  · intro y _ hy
    have hne : ¬ ((y : ℕ) = (x.val + 1) % (2 * n)) := fun hcond =>
      hy (Fin.ext (by rw [ringSucc_val]; exact hcond))
    rw [ringCoupling, if_neg hne, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

end LatticeSystem.Quantum

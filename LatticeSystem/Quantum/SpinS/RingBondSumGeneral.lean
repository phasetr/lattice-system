/-
The ring Heisenberg Hamiltonian as a bond sum, on a ring of any length
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

On a ring `Fin L` of any length, the directed nearest-neighbor coupling collapses the defining
double sum of `heisenbergHamiltonianS (ringCoupling L)` to a single sum over the bonds `(x, x+1)`:
`Ĥ = Σ_x Ŝ_x · Ŝ_{x+1}`, where `x + 1` is the cyclic successor `finRotate L x`.  This is the
bond-sum form used to localize `[Ĥ, Ŝ_z^{(3)}]` to the two bonds incident to `z`.
-/
import LatticeSystem.Quantum.SpinS.ShastryNoSSB
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisOrthogonality

namespace LatticeSystem.Quantum

open Matrix

/-- **The ring Heisenberg Hamiltonian as a bond sum (any length)**:
`heisenbergHamiltonianS (ringCoupling L) N = Σ_x Ŝ_x · Ŝ_{finRotate L x}`. -/
theorem heisenbergHamiltonianS_ringCoupling_eq_bondSum_general (L N : ℕ) [NeZero L] :
    heisenbergHamiltonianS (ringCoupling L) N
      = ∑ x : Fin L, spinSDot x (finRotate L x) N := by
  rw [heisenbergHamiltonianS_def]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (finRotate L x)]
  · rw [ringCoupling, if_pos (val_finRotate L x), one_smul]
  · intro y _ hy
    have hne : ¬ ((y : ℕ) = (x.val + 1) % L) := fun hcond =>
      hy (Fin.ext (by rw [val_finRotate]; exact hcond))
    rw [ringCoupling, if_neg hne, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

end LatticeSystem.Quantum

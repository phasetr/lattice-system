import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.TotalSquared

/-!
# Heisenberg Hamiltonian with uniform coupling equals the Casimir

For the trivial uniform coupling `J(x, y) = 1`, the Heisenberg
Hamiltonian coincides with the total-spin Casimir:

  `heisenbergHamiltonianS (fun _ _ => 1) N = totalSpinSSquared V N`.

Direct from `heisenbergHamiltonianS J N = ∑_{x, y} J(x, y) • Ŝ_x · Ŝ_y`
(definition) and `totalSpinSSquared = ∑_{x, y} Ŝ_x · Ŝ_y`
(`totalSpinSSquared_eq_sum_spinSDot`).

This is the operator-level form of the standard textbook fact that
"sum of all pair couplings = total-spin Casimir" on the multi-site
Hilbert space.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `heisenbergHamiltonianS (fun _ _ => 1) N = totalSpinSSquared V N`. -/
theorem heisenbergHamiltonianS_uniform_eq_totalSpinSSquared :
    (heisenbergHamiltonianS (fun (_ : V) (_ : V) => (1 : ℂ)) N :
      ManyBodyOpS V N) = totalSpinSSquared V N := by
  unfold heisenbergHamiltonianS
  rw [totalSpinSSquared_eq_sum_spinSDot]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [one_smul]

end LatticeSystem.Quantum

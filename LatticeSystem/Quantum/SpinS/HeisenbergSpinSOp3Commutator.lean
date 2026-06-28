/-
The Heisenberg Hamiltonian commutator with a single-site `Ŝ^{(3)}` distributes over bonds
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

The commutator of the Heisenberg Hamiltonian `Ĥ_J = Σ_x Σ_y J_{xy} Ŝ_x · Ŝ_y` with a single-site
`Ŝ_z^{(3)}` distributes over the bonds: `[Ĥ_J, Ŝ_z^{(3)}] = Σ_x Σ_y J_{xy} [Ŝ_x · Ŝ_y, Ŝ_z^{(3)}]`.
Combined with the per-bond commutator case analysis (left/right endpoint, off-bond) this reduces the
spin-current divergence `[Ĥ, Ŝ_z^{(3)}]` to the two bonds incident to `z`, the quantity entering the
double commutator of the infrared / f-sum-rule bound.
-/
import LatticeSystem.Quantum.SpinS.SingleBondSpinSOp3Commutator
import LatticeSystem.Quantum.SpinS.HeisenbergCore

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **The Heisenberg Hamiltonian commutator distributes over bonds**:
`[Ĥ_J, onSiteS z A] = Σ_x Σ_y J_{xy} [Ŝ_x · Ŝ_y, onSiteS z A]`. -/
theorem heisenbergHamiltonianS_commutator_onSiteS (J : Λ → Λ → ℂ) (z : Λ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    heisenbergHamiltonianS J N * onSiteS z A - onSiteS z A * heisenbergHamiltonianS J N
      = ∑ x : Λ, ∑ y : Λ,
          J x y • (spinSDot x y N * onSiteS z A - onSiteS z A * spinSDot x y N) := by
  rw [heisenbergHamiltonianS_def, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, smul_sub]

end LatticeSystem.Quantum

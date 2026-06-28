/-
The ring Hamiltonian–`Ŝ^{(3)}` commutator as a bond sum
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Writing the ring Heisenberg Hamiltonian as a bond sum, its commutator with a single-site `Ŝ_z^{(3)}`
distributes over the bonds: `[Ĥ, Ŝ_z^{(3)}] = Σ_x [Ŝ_x · Ŝ_{x+1}, Ŝ_z^{(3)}]`.  Since each bond
commutator vanishes unless `z` lies on the bond, this localizes `[Ĥ, Ŝ_z^{(3)}]` to the two bonds
incident to `z` — the spin-current divergence entering the f-sum-rule oscillator strength.
-/
import LatticeSystem.Quantum.SpinS.RingBondSumGeneral

namespace LatticeSystem.Quantum

open Matrix

/-- **The ring Hamiltonian commutator with `Ŝ_z^{(3)}` as a bond sum**:
`[Ĥ, Ŝ_z^{(3)}] = Σ_x (Ŝ_x · Ŝ_{x+1}) Ŝ_z^{(3)} − Ŝ_z^{(3)} (Ŝ_x · Ŝ_{x+1})`. -/
theorem heisenbergHamiltonianS_ringCoupling_commutator_onSiteS_spinSOp3 (L N : ℕ) [NeZero L]
    (z : Fin L) :
    heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
        - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N
      = ∑ x : Fin L, (spinSDot x (finRotate L x) N * onSiteS z (spinSOp3 N)
          - onSiteS z (spinSOp3 N) * spinSDot x (finRotate L x) N) := by
  rw [heisenbergHamiltonianS_ringCoupling_eq_bondSum_general, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]

end LatticeSystem.Quantum

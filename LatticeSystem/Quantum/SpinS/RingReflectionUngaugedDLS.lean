/-
The ungauged Dyson–Lieb–Simon split of the ring Heisenberg Hamiltonian
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 23).

Combining the bond split (`heisenbergHamiltonianS_ringCoupling_bond_split`) with the identification
of the right bonds as the reflected left bonds (`ringRightBondSum_eq_theta`) gives the ungauged DLS
form of the ring Heisenberg Hamiltonian:
`heisenbergHamiltonianS (ringCoupling (2n)) = H_L + θ(H_L) + (Ŝ_{n−1}·Ŝ_n + Ŝ_{2n−1}·Ŝ_0)`,
with `H_L = ringLeftHamiltonian`.  The crossing term here is the *ungauged* antiferromagnetic
crossing bond; it differs from the gauged `crossBondInteractionS` (which has the `Ŝ²` sign flipped)
by the DLS/Marshall gauge.  Bridging the two via the gauge unitary is the next step.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionRightEqTheta

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **The ungauged DLS split of the ring Heisenberg Hamiltonian.** -/
theorem heisenbergHamiltonianS_ringCoupling_ungauged_dls (n N : ℕ) [NeZero n] :
    heisenbergHamiltonianS (ringCoupling (2 * n)) N
      = ringLeftHamiltonian n N + ringReflectionThetaS n N (ringLeftHamiltonian n N)
        + (spinSDot (⟨n - 1, by have := NeZero.ne n; omega⟩ : Fin (2 * n))
              (ringBondSucc n ⟨n - 1, by have := NeZero.ne n; omega⟩) N
            + spinSDot (⟨2 * n - 1, by have := NeZero.ne n; omega⟩ : Fin (2 * n))
              (ringBondSucc n ⟨2 * n - 1, by have := NeZero.ne n; omega⟩) N) := by
  rw [heisenbergHamiltonianS_ringCoupling_bond_split, ringRightBondSum_eq_theta]
  abel

end LatticeSystem.Quantum

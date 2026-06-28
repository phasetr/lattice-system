/-
The concrete gauged ring antiferromagnet has a reflection-positive Gibbs weight
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 20).

Instantiating the ring DLS decomposition with the concrete left part `H_L = ringLeftHamiltonian`
(the left-half bond sum, which is left-supported) and applying the Gibbs capstone shows that the
gauged ring Gibbs weight `exp(−β·H)` is a reflection-positive trace weight, where `H` is
`ringLeftHamiltonian + θ(ringLeftHamiltonian) − (crossBondInteractionS 0 + crossBondInteractionS (n−1))`.
This `H` is the gauged ring antiferromagnetic Hamiltonian (left bonds + reflected right bonds +
gauged crossing bonds); its identification with the physical ungauged Hamiltonian is the next step.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionRingInstance
import LatticeSystem.Quantum.SpinS.RingReflectionLeftHamiltonian

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- The DLS decomposition of the gauged ring antiferromagnet with the concrete left part
`ringLeftHamiltonian` (the left-half bond sum). -/
noncomputable def ringDLSDecomposition (n N : ℕ) [NeZero n] : RPDecomposition n N :=
  ringCrossingRPDecomposition (ringLeftHamiltonian n N) ringLeftHamiltonian_supportedOnLeft

/-- The reconstructed gauged ring Hamiltonian: left bonds, reflected right bonds, and the gauged
crossing bonds at sites `0` and `n − 1`. -/
theorem ringDLSDecomposition_toHamiltonian (n N : ℕ) [NeZero n] :
    (ringDLSDecomposition n N).toHamiltonian
      = ringLeftHamiltonian n N + ringReflectionThetaS n N (ringLeftHamiltonian n N)
        - (crossBondInteractionS (ringCrossingSite n 0) N
          + crossBondInteractionS (ringCrossingSite n 1) N) :=
  ringCrossingRPDecomposition_toHamiltonian (ringLeftHamiltonian n N)
    ringLeftHamiltonian_supportedOnLeft

/-- **The gauged ring antiferromagnet has a reflection-positive Gibbs weight.**  For `β ≥ 0`,
`exp(−β·H)` of the gauged ring Hamiltonian is a reflection-positive trace weight. -/
theorem ringDLSDecomposition_gibbs_rpTraceWeight (n N : ℕ) [NeZero n] {β : ℝ} (hβ : 0 ≤ β) :
    RPTraceWeightS n N (NormedSpace.exp (-(β : ℂ) • (ringDLSDecomposition n N).toHamiltonian)) :=
  (ringDLSDecomposition n N).gibbs_rpTraceWeight hβ

end LatticeSystem.Quantum

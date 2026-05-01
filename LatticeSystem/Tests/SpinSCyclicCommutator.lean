import LatticeSystem.Quantum.SpinS.CyclicCommutator

/-!
# Test coverage for the spin-`S` cyclic SU(2) commutator
(Tasaki §2.1 P1d''' β-20)
-/

namespace LatticeSystem.Tests.SpinSCyclicCommutator

open LatticeSystem.Quantum

/-- `[Ŝ^{(1)}, Ŝ^{(2)}] = i · Ŝ^{(3)}`. -/
example (N : ℕ) :
    spinSOp1 N * spinSOp2 N - spinSOp2 N * spinSOp1 N =
      Complex.I • spinSOp3 N :=
  spinSOp1_commutator_spinSOp2 N

end LatticeSystem.Tests.SpinSCyclicCommutator

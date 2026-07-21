import LatticeSystem.Quantum.SpinS.CyclicCommutator

/-!
# Test coverage for the spin-`S` cyclic SU(2) commutators
(Tasaki §2.1 P1d''' β-20, β-21, β-22)
-/

namespace LatticeSystem.Tests.SpinSCyclicCommutator

open LatticeSystem.Quantum

/-- `[Ŝ^{(1)}, Ŝ^{(2)}] = i · Ŝ^{(3)}`. -/
example (N : ℕ) :
    spinSOp1 N * spinSOp2 N - spinSOp2 N * spinSOp1 N =
      Complex.I • spinSOp3 N :=
  spinSOp1_commutator_spinSOp2 N

/-- `[Ŝ^{(2)}, Ŝ^{(3)}] = i · Ŝ^{(1)}`. -/
example (N : ℕ) :
    spinSOp2 N * spinSOp3 N - spinSOp3 N * spinSOp2 N =
      Complex.I • spinSOp1 N :=
  spinSOp2_commutator_spinSOp3 N

/-- `[Ŝ^{(3)}, Ŝ^{(1)}] = i · Ŝ^{(2)}`. -/
example (N : ℕ) :
    spinSOp3 N * spinSOp1 N - spinSOp1 N * spinSOp3 N =
      Complex.I • spinSOp2 N :=
  spinSOp3_commutator_spinSOp1 N

end LatticeSystem.Tests.SpinSCyclicCommutator

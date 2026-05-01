import LatticeSystem.Quantum.SpinS.Algebra

/-!
# Test coverage for the spin-`S` Cartan relations (Tasaki §2.1 P1d''' β-2)
-/

namespace LatticeSystem.Tests.SpinSAlgebra

open LatticeSystem.Quantum

/-- Cartan relation: `[Ŝ^{(3)}, Ŝ^+] = Ŝ^+`. -/
example (N : ℕ) :
    spinSOp3 N * spinSOpPlus N - spinSOpPlus N * spinSOp3 N = spinSOpPlus N :=
  spinSOp3_commutator_spinSOpPlus N

/-- Cartan relation: `[Ŝ^{(3)}, Ŝ^-] = -Ŝ^-`. -/
example (N : ℕ) :
    spinSOp3 N * spinSOpMinus N - spinSOpMinus N * spinSOp3 N =
      -spinSOpMinus N :=
  spinSOp3_commutator_spinSOpMinus N

end LatticeSystem.Tests.SpinSAlgebra

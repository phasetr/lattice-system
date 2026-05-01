import LatticeSystem.Quantum.SpinS.CasimirInvariance

/-!
# Test coverage for the spin-`S` Casimir invariance
(Tasaki §2.1 P1d''' β-18)
-/

namespace LatticeSystem.Tests.SpinSCasimirInvariance

open LatticeSystem.Quantum

/-- `Ŝ^{(1)}` commutes with `(Ŝ)²`. -/
example (N : ℕ) :
    Commute (spinSOp1 N)
      (spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N + spinSOp3 N * spinSOp3 N) :=
  spinSOp1_commute_total_squared N

/-- `Ŝ^{(3)}` commutes with `(Ŝ)²`. -/
example (N : ℕ) :
    Commute (spinSOp3 N)
      (spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N + spinSOp3 N * spinSOp3 N) :=
  spinSOp3_commute_total_squared N

/-- `Ŝ^+` commutes with `(Ŝ)²`. -/
example (N : ℕ) :
    Commute (spinSOpPlus N)
      (spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N + spinSOp3 N * spinSOp3 N) :=
  spinSOpPlus_commute_total_squared N

end LatticeSystem.Tests.SpinSCasimirInvariance

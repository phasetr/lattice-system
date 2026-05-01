import LatticeSystem.Quantum.SpinS.Casimir

/-!
# Test coverage for the spin-`S` Casimir identity (Tasaki §2.1 P1d''' β-14)
-/

namespace LatticeSystem.Tests.SpinSCasimir

open LatticeSystem.Quantum

/-- `(Ŝ^{(1)})² + (Ŝ^{(2)})² = (1/2) · (Ŝ^+ · Ŝ^- + Ŝ^- · Ŝ^+)`. -/
example (N : ℕ) :
    spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N =
      (1/2 : ℂ) • (spinSOpPlus N * spinSOpMinus N +
        spinSOpMinus N * spinSOpPlus N) :=
  spinSOp1_sq_add_spinSOp2_sq N

/-- **Casimir identity**: `(Ŝ^{(1)})² + (Ŝ^{(2)})² + (Ŝ^{(3)})² = (N(N+2)/4) · 1`. -/
example (N : ℕ) :
    spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N + spinSOp3 N * spinSOp3 N =
      ((N : ℂ) * ((N : ℂ) + 2) / 4) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :=
  spinSOp_total_squared N

end LatticeSystem.Tests.SpinSCasimir

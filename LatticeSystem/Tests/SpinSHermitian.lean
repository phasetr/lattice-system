import LatticeSystem.Quantum.SpinS.Hermitian

/-!
# Test coverage for spin-`S` Hermiticity (Tasaki §2.1 P1d''' β-3)
-/

namespace LatticeSystem.Tests.SpinSHermitian

open LatticeSystem.Quantum

/-- `(Ŝ^+)ᴴ = Ŝ^-`. -/
example (N : ℕ) :
    Matrix.conjTranspose (spinSOpPlus N) = spinSOpMinus N :=
  spinSOpPlus_conjTranspose N

/-- `(Ŝ^-)ᴴ = Ŝ^+`. -/
example (N : ℕ) :
    Matrix.conjTranspose (spinSOpMinus N) = spinSOpPlus N :=
  spinSOpMinus_conjTranspose N

/-- `Ŝ^{(1)}` is Hermitian. -/
example (N : ℕ) : Matrix.IsHermitian (spinSOp1 N) := spinSOp1_isHermitian N

/-- `Ŝ^{(2)}` is Hermitian. -/
example (N : ℕ) : Matrix.IsHermitian (spinSOp2 N) := spinSOp2_isHermitian N

/-- `Ŝ^{(3)}` is Hermitian. -/
example (N : ℕ) : Matrix.IsHermitian (spinSOp3 N) := spinSOp3_isHermitian N

end LatticeSystem.Tests.SpinSHermitian

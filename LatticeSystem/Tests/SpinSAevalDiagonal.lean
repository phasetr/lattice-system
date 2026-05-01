import LatticeSystem.Quantum.SpinS.AevalDiagonal

/-!
# Test coverage for `aeval_diagonal` (Tasaki §2.1 P1d''' β-24)
-/

namespace LatticeSystem.Tests.SpinSAevalDiagonal

open LatticeSystem.Quantum

/-- `aeval (diagonal v) p = diagonal (fun i => p.eval (v i))`. -/
example {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommSemiring R]
    (v : n → R) (p : Polynomial R) :
    Polynomial.aeval (Matrix.diagonal v) p =
      Matrix.diagonal (fun i : n => p.eval (v i)) :=
  aeval_diagonal v p

end LatticeSystem.Tests.SpinSAevalDiagonal

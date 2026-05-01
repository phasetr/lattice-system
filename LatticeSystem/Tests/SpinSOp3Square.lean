import LatticeSystem.Quantum.SpinS.Op3Square

/-!
# Test coverage for `(Ŝ^{(3)})²` (Tasaki §2.1 P1d''' β-11)
-/

namespace LatticeSystem.Tests.SpinSOp3Square

open LatticeSystem.Quantum

/-- `(Ŝ^{(3)})² = diag((N/2 − i)²)`. -/
example (N : ℕ) :
    spinSOp3 N * spinSOp3 N =
      Matrix.diagonal (fun i : Fin (N + 1) =>
        ((N : ℂ) / 2 - (i.val : ℂ)) * ((N : ℂ) / 2 - (i.val : ℂ))) :=
  spinSOp3_sq_eq_diagonal N

end LatticeSystem.Tests.SpinSOp3Square

/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.MinusPlusDiag

/-!
# Test coverage for `Ŝ^- · Ŝ^+` diagonal formula (Tasaki §2.1 P1d''' β-13)
-/

namespace LatticeSystem.Tests.SpinSMinusPlusDiag

open LatticeSystem.Quantum

/-- `Ŝ^- · Ŝ^+ = diag(i · (N − i + 1))`. -/
example (N : ℕ) :
    spinSOpMinus N * spinSOpPlus N =
      Matrix.diagonal (fun i : Fin (N + 1) =>
        (((i.val : ℂ)) * ((N : ℂ) - (i.val : ℂ) + 1))) :=
  spinSOpMinus_mul_spinSOpPlus_eq_diagonal N

end LatticeSystem.Tests.SpinSMinusPlusDiag

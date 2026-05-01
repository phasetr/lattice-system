/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.PlusMinusDiag

/-!
# Test coverage for `Ŝ^+ · Ŝ^-` diagonal formula (Tasaki §2.1 P1d''' β-12)
-/

namespace LatticeSystem.Tests.SpinSPlusMinusDiag

open LatticeSystem.Quantum

/-- `Ŝ^+ · Ŝ^- = diag((i + 1)(N − i))`. -/
example (N : ℕ) :
    spinSOpPlus N * spinSOpMinus N =
      Matrix.diagonal (fun i : Fin (N + 1) =>
        (((i.val : ℂ) + 1) * ((N : ℂ) - (i.val : ℂ)))) :=
  spinSOpPlus_mul_spinSOpMinus_eq_diagonal N

end LatticeSystem.Tests.SpinSPlusMinusDiag

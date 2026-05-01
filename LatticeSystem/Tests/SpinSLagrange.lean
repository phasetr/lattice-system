/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.Lagrange

/-!
# Test coverage for spin-`S` eigenvalue equation `Ŝ^{(3)} · P_k = λ_k · P_k`
(Tasaki §2.1 P1d''' β-5)
-/

namespace LatticeSystem.Tests.SpinSLagrange

open LatticeSystem.Quantum

/-- `Ŝ^{(3)} · P_k = λ_k · P_k`. -/
example (N : ℕ) (k : Fin (N + 1)) :
    spinSOp3 N * spinSDiagProj N k =
      (((N : ℂ) / 2 - (k.val : ℂ)) • spinSDiagProj N k) :=
  spinSOp3_mul_diagProj N k

/-- `P_k · Ŝ^{(3)} = λ_k · P_k`. -/
example (N : ℕ) (k : Fin (N + 1)) :
    spinSDiagProj N k * spinSOp3 N =
      (((N : ℂ) / 2 - (k.val : ℂ)) • spinSDiagProj N k) :=
  diagProj_mul_spinSOp3 N k

/-- `Ŝ^{(3)}` and `P_k` commute. -/
example (N : ℕ) (k : Fin (N + 1)) :
    Commute (spinSOp3 N) (spinSDiagProj N k) :=
  spinSOp3_commute_diagProj N k

end LatticeSystem.Tests.SpinSLagrange

/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.LagrangeFormula

/-!
# Test coverage for the spin-`S` Lagrange-interpolation formula
(Tasaki §2.1 P1d''' β-25)
-/

namespace LatticeSystem.Tests.SpinSLagrangeFormula

open LatticeSystem.Quantum

/-- `P_k = aeval (Ŝ^{(3)}) (Lagrange.basis Finset.univ (spinSOp3Eigen N) k)`. -/
example (N : ℕ) (k : Fin (N + 1)) :
    spinSDiagProj N k =
      Polynomial.aeval (spinSOp3 N)
        (Lagrange.basis (Finset.univ : Finset (Fin (N + 1)))
          (spinSOp3Eigen N) k) :=
  spinSDiagProj_eq_lagrange_aeval N k

end LatticeSystem.Tests.SpinSLagrangeFormula

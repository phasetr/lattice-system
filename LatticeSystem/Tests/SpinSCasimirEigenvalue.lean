/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.CasimirEigenvalue

/-!
# Test coverage for the spin-`S` Casimir eigenvalue on basis vectors
(Tasaki §2.1 P1d''' β-17)
-/

namespace LatticeSystem.Tests.SpinSCasimirEigenvalue

open LatticeSystem.Quantum

/-- `(Ŝ)² · |k⟩ = (N(N+2)/4) · |k⟩`. -/
example (N : ℕ) (k : Fin (N + 1)) :
    (spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N +
        spinSOp3 N * spinSOp3 N).mulVec (Pi.single k 1) =
      ((N : ℂ) * ((N : ℂ) + 2) / 4) • (Pi.single k 1 : Fin (N + 1) → ℂ) :=
  spinSOp_total_squared_mulVec_basis N k

end LatticeSystem.Tests.SpinSCasimirEigenvalue

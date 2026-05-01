/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.AllUnitsAdjoin

/-!
# Test coverage for `Matrix.single i j 1 ∈ Algebra.adjoin ℂ {Ŝ^{(α)}}`
(Tasaki §2.1 P1d''' β-31)
-/

namespace LatticeSystem.Tests.SpinSAllUnitsAdjoin

open LatticeSystem.Quantum

/-- Every matrix unit lies in the spin-operator subalgebra. -/
example (N : ℕ) (i j : Fin (N + 1)) :
    Matrix.single i j (1 : ℂ) ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
  matrix_single_mem_adjoin i j

end LatticeSystem.Tests.SpinSAllUnitsAdjoin

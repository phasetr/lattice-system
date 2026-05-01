/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.CyclicCommutator23

/-!
# Test coverage for the second cyclic SU(2) commutator
(Tasaki §2.1 P1d''' β-21)
-/

namespace LatticeSystem.Tests.SpinSCyclicCommutator23

open LatticeSystem.Quantum

/-- `[Ŝ^{(2)}, Ŝ^{(3)}] = i · Ŝ^{(1)}`. -/
example (N : ℕ) :
    spinSOp2 N * spinSOp3 N - spinSOp3 N * spinSOp2 N =
      Complex.I • spinSOp1 N :=
  spinSOp2_commutator_spinSOp3 N

end LatticeSystem.Tests.SpinSCyclicCommutator23

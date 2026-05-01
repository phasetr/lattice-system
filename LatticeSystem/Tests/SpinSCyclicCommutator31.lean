/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.CyclicCommutator31

/-!
# Test coverage for the third cyclic SU(2) commutator
(Tasaki §2.1 P1d''' β-22)
-/

namespace LatticeSystem.Tests.SpinSCyclicCommutator31

open LatticeSystem.Quantum

/-- `[Ŝ^{(3)}, Ŝ^{(1)}] = i · Ŝ^{(2)}`. -/
example (N : ℕ) :
    spinSOp3 N * spinSOp1 N - spinSOp1 N * spinSOp3 N =
      Complex.I • spinSOp2 N :=
  spinSOp3_commutator_spinSOp1 N

end LatticeSystem.Tests.SpinSCyclicCommutator31

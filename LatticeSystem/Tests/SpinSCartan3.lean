/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.Cartan3

/-!
# Test coverage for the third Cartan relation `[Ŝ^+, Ŝ^-] = 2 · Ŝ^{(3)}`
(Tasaki §2.1 P1d''' β-19)
-/

namespace LatticeSystem.Tests.SpinSCartan3

open LatticeSystem.Quantum

/-- `[Ŝ^+, Ŝ^-] = 2 · Ŝ^{(3)}`. -/
example (N : ℕ) :
    spinSOpPlus N * spinSOpMinus N - spinSOpMinus N * spinSOpPlus N =
      (2 : ℂ) • spinSOp3 N :=
  spinSOpPlus_commutator_spinSOpMinus N

end LatticeSystem.Tests.SpinSCartan3

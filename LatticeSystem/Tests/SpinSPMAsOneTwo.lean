/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.PMAsOneTwo

/-!
# Test coverage for `Ŝ^± = Ŝ^{(1)} ± i · Ŝ^{(2)}`
(Tasaki §2.1 P1d''' β-26)
-/

namespace LatticeSystem.Tests.SpinSPMAsOneTwo

open LatticeSystem.Quantum

/-- `Ŝ^+ = Ŝ^{(1)} + i · Ŝ^{(2)}`. -/
example (N : ℕ) :
    spinSOpPlus N = spinSOp1 N + Complex.I • spinSOp2 N :=
  spinSOpPlus_eq_one_add_I_smul_two N

/-- `Ŝ^- = Ŝ^{(1)} − i · Ŝ^{(2)}`. -/
example (N : ℕ) :
    spinSOpMinus N = spinSOp1 N - Complex.I • spinSOp2 N :=
  spinSOpMinus_eq_one_sub_I_smul_two N

end LatticeSystem.Tests.SpinSPMAsOneTwo

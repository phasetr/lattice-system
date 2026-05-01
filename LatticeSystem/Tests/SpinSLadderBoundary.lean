/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.LadderBoundary

/-!
# Test coverage for the spin-`S` ladder boundary annihilation
(Tasaki §2.1 P1d''' β-8)
-/

namespace LatticeSystem.Tests.SpinSLadderBoundary

open LatticeSystem.Quantum

/-- First column of `Ŝ^+` is zero. -/
example (N : ℕ) (i : Fin (N + 1)) :
    spinSOpPlus N i ⟨0, Nat.succ_pos N⟩ = 0 :=
  spinSOpPlus_apply_first_col i

/-- Last column of `Ŝ^-` is zero. -/
example (N : ℕ) (i : Fin (N + 1)) :
    spinSOpMinus N i (Fin.last N) = 0 :=
  spinSOpMinus_apply_last_col i

/-- Top of ladder: `Ŝ^+ · P_0 = 0`. -/
example (N : ℕ) :
    spinSOpPlus N * spinSDiagProj N ⟨0, Nat.succ_pos N⟩ = 0 :=
  spinSOpPlus_mul_diagProj_first

/-- Bottom of ladder: `Ŝ^- · P_N = 0`. -/
example (N : ℕ) :
    spinSOpMinus N * spinSDiagProj N (Fin.last N) = 0 :=
  spinSOpMinus_mul_diagProj_last

end LatticeSystem.Tests.SpinSLadderBoundary

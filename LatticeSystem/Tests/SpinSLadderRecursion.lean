/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.LadderRecursion

/-!
# Test coverage for the spin-`S` ladder recursion (Tasaki §2.1 P1d''' β-7)
-/

namespace LatticeSystem.Tests.SpinSLadderRecursion

open LatticeSystem.Quantum

/-- Ladder recursion: `Ŝ^+ · P_{k+1} · Ŝ^- = (k + 1)(N − k) · P_k`. -/
example (N : ℕ) (k : Fin (N + 1)) (h : k.val + 1 < N + 1) :
    spinSOpPlus N * spinSDiagProj N ⟨k.val + 1, h⟩ * spinSOpMinus N =
      (((k.val : ℂ) + 1) * ((N : ℂ) - (k.val : ℂ))) • spinSDiagProj N k :=
  spinSOpPlus_mul_diagProj_succ_mul_spinSOpMinus k h

end LatticeSystem.Tests.SpinSLadderRecursion

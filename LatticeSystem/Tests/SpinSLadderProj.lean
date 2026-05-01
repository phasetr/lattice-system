/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.LadderProj

/-!
# Test coverage for the spin-`S` ladder action on diagonal projectors
(Tasaki §2.1 P1d''' β-6)
-/

namespace LatticeSystem.Tests.SpinSLadderProj

open LatticeSystem.Quantum

/-- Right multiplication by `P_k` selects column `k`. -/
example (N : ℕ) (k : Fin (N + 1))
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (i j : Fin (N + 1)) :
    (A * spinSDiagProj N k) i j = if j = k then A i k else 0 :=
  mul_diagProj_apply k A i j

/-- Left multiplication by `P_k` selects row `k`. -/
example (N : ℕ) (k : Fin (N + 1))
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (i j : Fin (N + 1)) :
    (spinSDiagProj N k * A) i j = if i = k then A k j else 0 :=
  diagProj_mul_apply k A i j

/-- `(Ŝ^+ · P_k)[i, j] = if j = k then Ŝ^+[i, k] else 0`. -/
example (N : ℕ) (k : Fin (N + 1)) (i j : Fin (N + 1)) :
    (spinSOpPlus N * spinSDiagProj N k) i j =
      if j = k then spinSOpPlus N i k else 0 :=
  spinSOpPlus_mul_diagProj_apply k i j

end LatticeSystem.Tests.SpinSLadderProj

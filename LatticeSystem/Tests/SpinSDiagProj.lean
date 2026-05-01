/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.DiagProj

/-!
# Test coverage for spin-`S` diagonal projectors (Tasaki §2.1 P1d''' β-4)
-/

namespace LatticeSystem.Tests.SpinSDiagProj

open LatticeSystem.Quantum

/-- Diagonal-projector value at the diagonal index. -/
example (N : ℕ) (k : Fin (N + 1)) : spinSDiagProj N k k k = 1 :=
  spinSDiagProj_apply_diag k

/-- Eigenvalue action of the shifted operator on the projector. -/
example (N : ℕ) (k j : Fin (N + 1)) :
    (spinSOp3 N - (((N : ℂ) / 2 - (j.val : ℂ)) •
        (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ))) *
      spinSDiagProj N k =
      ((j.val : ℂ) - (k.val : ℂ)) • spinSDiagProj N k :=
  spinSOp3_sub_smul_mul_diagProj N k j

/-- Annihilation: at `j = k` the shifted operator annihilates `P_k`. -/
example (N : ℕ) (k : Fin (N + 1)) :
    (spinSOp3 N - (((N : ℂ) / 2 - (k.val : ℂ)) •
        (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ))) *
      spinSDiagProj N k = 0 :=
  spinSOp3_sub_smul_self_mul_diagProj N k

end LatticeSystem.Tests.SpinSDiagProj

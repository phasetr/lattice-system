/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.DiagProjProperties

/-!
# Test coverage for spin-`S` diagonal-projector properties
(Tasaki §2.1 P1d''' β-9)
-/

namespace LatticeSystem.Tests.SpinSDiagProjProperties

open LatticeSystem.Quantum

/-- `P_k` is Hermitian. -/
example (N : ℕ) (k : Fin (N + 1)) :
    Matrix.IsHermitian (spinSDiagProj N k) :=
  spinSDiagProj_isHermitian k

/-- `Σ_k P_k = 1` (resolution of the identity). -/
example (N : ℕ) :
    ∑ k : Fin (N + 1), spinSDiagProj N k =
      (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :=
  sum_spinSDiagProj_eq_one

end LatticeSystem.Tests.SpinSDiagProjProperties

import LatticeSystem.Quantum.SpinS.DiagProjOrtho

/-!
# Test coverage for spin-`S` diagonal-projector idempotence and orthogonality
(Tasaki §2.1 P1d''' β-23)
-/

namespace LatticeSystem.Tests.SpinSDiagProjOrtho

open LatticeSystem.Quantum

/-- Idempotence: `P_k · P_k = P_k`. -/
example (N : ℕ) (k : Fin (N + 1)) :
    spinSDiagProj N k * spinSDiagProj N k = spinSDiagProj N k :=
  spinSDiagProj_mul_self N k

/-- Orthogonality: `P_i · P_j = 0` for `i ≠ j`. -/
example (N : ℕ) {i j : Fin (N + 1)} (h : i ≠ j) :
    spinSDiagProj N i * spinSDiagProj N j = 0 :=
  spinSDiagProj_mul_of_ne N h

end LatticeSystem.Tests.SpinSDiagProjOrtho

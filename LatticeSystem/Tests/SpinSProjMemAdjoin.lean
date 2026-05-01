import LatticeSystem.Quantum.SpinS.ProjMemAdjoin

/-!
# Test coverage for `P_k ∈ Algebra.adjoin ℂ {Ŝ^{(α)}}`
(Tasaki §2.1 P1d''' β-27)
-/

namespace LatticeSystem.Tests.SpinSProjMemAdjoin

open LatticeSystem.Quantum

/-- `P_k ∈ Algebra.adjoin ℂ {Ŝ^{(3)}}`. -/
example (N : ℕ) (k : Fin (N + 1)) :
    spinSDiagProj N k ∈
      Algebra.adjoin ℂ
        ({spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
  spinSDiagProj_mem_adjoin_spinSOp3 N k

/-- `P_k ∈ Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`. -/
example (N : ℕ) (k : Fin (N + 1)) :
    spinSDiagProj N k ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
  spinSDiagProj_mem_adjoin N k

end LatticeSystem.Tests.SpinSProjMemAdjoin

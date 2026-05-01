import LatticeSystem.Quantum.SpinS.PMMemAdjoin

/-!
# Test coverage for `Ŝ^± ∈ Algebra.adjoin ℂ {Ŝ^{(α)}}`
(Tasaki §2.1 P1d''' β-28)
-/

namespace LatticeSystem.Tests.SpinSPMMemAdjoin

open LatticeSystem.Quantum

/-- `Ŝ^+ ∈ Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`. -/
example (N : ℕ) :
    spinSOpPlus N ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
  spinSOpPlus_mem_adjoin N

/-- `Ŝ^- ∈ Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`. -/
example (N : ℕ) :
    spinSOpMinus N ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
  spinSOpMinus_mem_adjoin N

end LatticeSystem.Tests.SpinSPMMemAdjoin

import LatticeSystem.Quantum.SpinS.OffsetUnitAdjoin

/-!
# Test coverage for `E_{i, i + (k+1)}, E_{i + (k+1), i} ∈ Algebra.adjoin ℂ {Ŝ^{(α)}}`
(Tasaki §2.1 P1d''' β-30)
-/

namespace LatticeSystem.Tests.SpinSOffsetUnitAdjoin

open LatticeSystem.Quantum

/-- Upper-stride matrix unit. -/
example (N : ℕ) (i : Fin (N + 1)) (k : ℕ) (h : i.val + (k + 1) < N + 1) :
    Matrix.single i (⟨i.val + (k + 1), h⟩ : Fin (N + 1)) (1 : ℂ) ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
  single_offset_succ_mem_adjoin i k h

/-- Lower-stride matrix unit. -/
example (N : ℕ) (i : Fin (N + 1)) (k : ℕ) (h : i.val + (k + 1) < N + 1) :
    Matrix.single (⟨i.val + (k + 1), h⟩ : Fin (N + 1)) i (1 : ℂ) ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
  single_offset_succ_swap_mem_adjoin i k h

end LatticeSystem.Tests.SpinSOffsetUnitAdjoin

/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.NeighborUnitAdjoin

/-!
# Test coverage for `E_{i, i+1}, E_{i+1, i} ∈ Algebra.adjoin ℂ {Ŝ^{(α)}}`
(Tasaki §2.1 P1d''' β-29)
-/

namespace LatticeSystem.Tests.SpinSNeighborUnitAdjoin

open LatticeSystem.Quantum

/-- Upper-immediate-neighbor unit. -/
example (N : ℕ) (i : Fin (N + 1)) (h : i.val + 1 < N + 1) :
    Matrix.single i (⟨i.val + 1, h⟩ : Fin (N + 1)) (1 : ℂ) ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
  single_succ_mem_adjoin i h

/-- Lower-immediate-neighbor unit. -/
example (N : ℕ) (i : Fin (N + 1)) (h : i.val + 1 < N + 1) :
    Matrix.single (⟨i.val + 1, h⟩ : Fin (N + 1)) i (1 : ℂ) ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
  single_succ_swap_mem_adjoin i h

end LatticeSystem.Tests.SpinSNeighborUnitAdjoin

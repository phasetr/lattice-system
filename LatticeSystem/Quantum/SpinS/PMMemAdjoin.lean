/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.PMAsOneTwo
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Raising / lowering operators live in `Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`
(Tasaki §2.1 P1d''' β-28)

By β-26, `Ŝ^± = Ŝ^{(1)} ± i · Ŝ^{(2)}`, so the ladder operators
are `ℂ`-linear combinations of the Cartesian generators. Hence:

  `Ŝ^+ ∈ Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`,
  `Ŝ^- ∈ Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`.

This complements β-27 (`P_k ∈ adjoin {Ŝ^{(α)}}`) by adding the
ladder operators to the membership picture; both are needed for
the off-diagonal-as-polynomial step (β-29+) and the spanning theorem.

Tracked in #458.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- `Ŝ^+ ∈ Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`. -/
theorem spinSOpPlus_mem_adjoin (N : ℕ) :
    spinSOpPlus N ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := by
  rw [spinSOpPlus_eq_one_add_I_smul_two]
  refine Subalgebra.add_mem _ ?_ ?_
  · exact Algebra.subset_adjoin (Set.mem_insert _ _)
  · refine Subalgebra.smul_mem _ ?_ _
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

/-- `Ŝ^- ∈ Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`. -/
theorem spinSOpMinus_mem_adjoin (N : ℕ) :
    spinSOpMinus N ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := by
  rw [spinSOpMinus_eq_one_sub_I_smul_two]
  refine Subalgebra.sub_mem _ ?_ ?_
  · exact Algebra.subset_adjoin (Set.mem_insert _ _)
  · refine Subalgebra.smul_mem _ ?_ _
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

end LatticeSystem.Quantum

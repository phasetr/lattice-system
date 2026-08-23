import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.CompleteLattice.Finset

/-!
# `finrank` of a finite indexed supremum of submodules (Theorem 10.4 arc, PR-14a)

Generic layer item for the Theorem 10.4 (Lieb repulsive Hubbard half-filling) discharge arc
(issue #5320, PR-14a). PR-14b's `Ŝ³`-decomposition step needs an upper bound
`finrank (⨆ i ∈ s, p i) ≤ Σ i ∈ s, finrank (p i)`; mathlib stops at the two-submodule case
(`Submodule.finrank_sup_add_finrank_inf_eq` and its corollary
`Submodule.finrank_add_le_finrank_add_finrank`). This file supplies the finite-indexed
generalization by induction on `s`, applying the two-submodule bound at each step.

## Main result

* `finrank_iSup_le_sum` — `finrank K (⨆ i ∈ s, p i) ≤ ∑ i ∈ s, finrank K (p i)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (Theorem 10.4), pp. 350–353.
-/

namespace LatticeSystem.Math

open Module

/-- **`finrank` of a finite indexed supremum is bounded by the sum of the `finrank`s.** By
induction on `s : Finset ι`, peeling off one index at a time and applying
`Submodule.finrank_add_le_finrank_add_finrank` at each step. -/
theorem finrank_iSup_le_sum {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (s : Finset ι) (p : ι → Submodule K V) :
    Module.finrank K (↥(⨆ i ∈ s, p i)) ≤ ∑ i ∈ s, Module.finrank K (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), p i) = (⊥ : Submodule K V) by simp]
    simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

end LatticeSystem.Math

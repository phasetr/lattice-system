import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# `finrank` of a finite indexed supremum of submodules (Theorem 10.4 arc, PR-14a)

Generic layer item for the Theorem 10.4 (Lieb repulsive Hubbard half-filling) discharge arc
(issue #5320, PR-14a). PR-14b's `Ŝ³`-decomposition step needs an upper bound
`finrank (⨆ i ∈ s, p i) ≤ Σ i ∈ s, finrank (p i)`; mathlib has no such lemma (checked: only
`Submodule.finrank_sup_add_finrank_inf_eq`, the two-submodule exact identity, is available). This
file supplies the finite-indexed generalization by induction on `s`, using the two-submodule
identity at each step (`finrank (p ⊔ q) ≤ finrank p + finrank q` since `finrank (p ⊓ q) ≥ 0`).

## Main result

* `finrank_iSup_le_sum` — `finrank K (⨆ i ∈ s, p i) ≤ ∑ i ∈ s, finrank K (p i)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (Theorem 10.4), pp. 350–353.
-/

namespace LatticeSystem.Math

open Module

/-- **`finrank` of a finite indexed supremum is bounded by the sum of the `finrank`s.** By
induction on `s : Finset ι`, peeling off one index at a time and applying
`Submodule.finrank_sup_add_finrank_inf_eq` at each step. -/
theorem finrank_iSup_le_sum {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (s : Finset ι) (p : ι → Submodule K V) :
    Module.finrank K (↥(⨆ i ∈ s, p i)) ≤ ∑ i ∈ s, Module.finrank K (p i) := by
  sorry

end LatticeSystem.Math

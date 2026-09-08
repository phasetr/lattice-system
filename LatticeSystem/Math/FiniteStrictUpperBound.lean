/-
A finite family of reals has a strict upper bound.

`Finite.exists_le` (`Mathlib.Data.Fintype.Order`) gives a non-strict upper bound for a family
indexed by any finite type; this module states the strict form, which is what a real matrix
diagonal (of a Hermitian operator on a finite-dimensional space) needs whenever a witness value
must be excluded from the spectrum by strict inequality. No `Nonempty` hypothesis on the index
type is required: the empty family is bounded by any real.
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Real.Basic

namespace LatticeSystem.Math

/-- **A finite family of reals has a strict upper bound.** `Finite.exists_le` is the only form
`mathlib` provides for a family indexed by an arbitrary finite type, and it is non-strict; adding
one to its bound makes it strict.  No `Nonempty ι` hypothesis is needed, unlike a
`Finset.sup'`-based witness. -/
theorem exists_gt_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) : ∃ c : ℝ, ∀ i, f i < c := by
  obtain ⟨b, hb⟩ := Finite.exists_le f
  exact ⟨b + 1, fun i => lt_of_le_of_lt (hb i) (lt_add_one b)⟩

end LatticeSystem.Math

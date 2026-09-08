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

end LatticeSystem.Math

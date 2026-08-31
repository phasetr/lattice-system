/-
Coordinate sup-norm balls in `ℤ^d`.

For a finite site set `Λ` carrying injective integer coordinates `pos : Λ → (Fin d → ℤ)`, the
**coordinate sup-norm ball** `B_r(x) = {y ∈ Λ : ∀ i, |pos y i - pos x i| ≤ r}` has cardinality at
most `(2r+1)^d`. This is the `d`-fold generalisation of the 1-D displacement-window count already
used at `Quantum/SpinS/LiebSchultzMattisGeneratorNorm.lean`, and it is the counting input needed
twice (at radius `r` and at radius `2r`) by Tasaki Problem 3.4.a, eq. (3.4.13).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, Problem 3.4.a, statement pp. 67-68, printed solution p. 501.

STATUS: header-only stub (TDD Red for PR-4 of the §3.4 arc, issue #5395). Declarations
`coordSupBall`, `mem_coordSupBall`, `card_coordSupBall_le` are introduced by a later commit of the
same PR.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.Abs

namespace LatticeSystem.Math

end LatticeSystem.Math

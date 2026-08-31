/-
Metric balls on a finite site set carrying an abstract `ℕ`-valued distance.

`siteBall dist r x` is the set of sites within distance `r` of `x`.  The only property the
double-commutator locality argument needs of `dist` is that balls of radius `r` around centres more
than `2r` apart are disjoint, which follows from symmetry and the triangle inequality alone; no
metric-space structure, no coordinate embedding, and no concrete lattice are assumed.

This is the geometric side of the locality bookkeeping, kept apart from `CoordinateBall.lean`,
whose ball is defined through an integer coordinate embedding and exists to *count*.  A concrete
distance supplies both: its balls carry the disjointness used in commutation arguments, and are
identified with coordinate balls when a cardinality bound is wanted.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, Problem 3.4.a, statement pp. 67-68.
-/
import Mathlib.Data.Fintype.Basic

namespace LatticeSystem.Math

variable {Λ : Type*} [Fintype Λ]

/-- The **ball** `B_r(x) = {y : dist y x ≤ r}` of radius `r` around the site `x`, for an abstract
`ℕ`-valued distance `dist` on a finite site set. -/
def siteBall (dist : Λ → Λ → ℕ) (r : ℕ) (x : Λ) : Finset Λ :=
  Finset.univ.filter fun y => dist y x ≤ r

/-- Membership in the ball is the distance bound. -/
theorem mem_siteBall {dist : Λ → Λ → ℕ} {r : ℕ} {x y : Λ} :
    y ∈ siteBall dist r x ↔ dist y x ≤ r := by
  simp [siteBall]

/-- **Well-separated centres have disjoint balls**: if `dist x y > 2r` then `B_r(x)` and `B_r(y)`
are disjoint, since a common point would join `x` to `y` by two arcs of length at most `r`.  This
is the only geometric input the locality argument needs, and it uses nothing about `dist` beyond
symmetry and the triangle inequality. -/
theorem disjoint_siteBall_of_lt {dist : Λ → Λ → ℕ}
    (hsymm : ∀ a b, dist a b = dist b a)
    (htri : ∀ a b c, dist a c ≤ dist a b + dist b c)
    {r : ℕ} {x y : Λ} (h : 2 * r < dist x y) :
    Disjoint (siteBall dist r x) (siteBall dist r y) := by
  refine Finset.disjoint_left.mpr fun w hwx hwy => ?_
  have h1 : dist w x ≤ r := mem_siteBall.mp hwx
  have h2 : dist w y ≤ r := mem_siteBall.mp hwy
  have hxy := htri x w y
  rw [hsymm x w] at hxy
  omega

end LatticeSystem.Math

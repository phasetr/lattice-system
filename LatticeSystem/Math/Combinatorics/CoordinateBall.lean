/-
Coordinate sup-norm balls in `ℤ^d`.

For a finite site set `Λ` carrying injective integer coordinates `pos : Λ → (Fin d → ℤ)`, the
**coordinate sup-norm ball** `B_r(x) = {y ∈ Λ : ∀ i, |pos y i - pos x i| ≤ r}` has cardinality at
most `(2r+1)^d`. This is the `d`-fold generalisation of the 1-D displacement-window count already
used at `Quantum/SpinS/LiebSchultzMattisGeneratorNorm.lean`, and it is the counting input needed
twice (at radius `r` and at radius `2r`) by Tasaki Problem 3.4.a, eq. (3.4.13).

The sup-norm reading of Tasaki's unqualified `|x - y| ≤ r` is chosen because the Euclidean ball is
contained in the sup-norm ball: a locality hypothesis phrased on the sup-norm ball is the weaker
one, and it is the reading under which the printed counts `(2r+1)^d` and `(4r+1)^d` are exact.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, Problem 3.4.a, statement pp. 67-68, printed solution p. 501.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.Abs

namespace LatticeSystem.Math

variable {Λ : Type*} [Fintype Λ] {d : ℕ}

/-- The **coordinate sup-norm ball** `B_r(x) = {y ∈ Λ : |pos y i - pos x i| ≤ r for every i}` of
radius `r` around the site `x`, for sites carrying integer coordinates `pos : Λ → (Fin d → ℤ)`. -/
def coordSupBall (pos : Λ → (Fin d → ℤ)) (r : ℕ) (x : Λ) : Finset Λ :=
  Finset.univ.filter fun y => ∀ i, |pos y i - pos x i| ≤ (r : ℤ)

/-- Membership in the coordinate sup-norm ball is the coordinate-wise displacement bound. -/
theorem mem_coordSupBall {pos : Λ → (Fin d → ℤ)} {r : ℕ} {x y : Λ} :
    y ∈ coordSupBall pos r x ↔ ∀ i, |pos y i - pos x i| ≤ (r : ℤ) := by
  simp [coordSupBall]

/-- **`d`-fold ball count**: `|B_r(x)| ≤ (2r+1)^d` whenever distinct sites carry distinct
coordinates.  Translating the ball to the origin, `y ↦ (i ↦ pos y i - pos x i)` is injective on it
and lands in the product of `d` copies of `Icc (-r) r`, of cardinality `(2r+1)^d`.

This single lemma supplies both counts Tasaki's solution of Problem 3.4.a performs: at radius `r`
it gives the `y`-count `(2r+1)^d`, and at radius `2 * r` it gives the `z`-count
`(2·(2r)+1)^d = (4r+1)^d`. -/
theorem card_coordSupBall_le (pos : Λ → (Fin d → ℤ)) (hpos : Function.Injective pos)
    (r : ℕ) (x : Λ) : (coordSupBall pos r x).card ≤ (2 * r + 1) ^ d := by
  classical
  have hmaps : ∀ y ∈ coordSupBall pos r x, (fun i => pos y i - pos x i) ∈
      Fintype.piFinset fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ) := by
    intro y hy
    refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
    have h := abs_le.mp (mem_coordSupBall.mp hy i)
    omega
  have hinj : Set.InjOn (fun y => fun i => pos y i - pos x i) (coordSupBall pos r x) := by
    intro y₁ _ y₂ _ hy
    refine hpos (funext fun i => ?_)
    have hi := congrFun hy i
    simp only at hi
    omega
  calc (coordSupBall pos r x).card
      ≤ (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (2 * r + 1) ^ d := by
        rw [Fintype.card_piFinset_const, Int.card_Icc]
        congr 1
        omega

end LatticeSystem.Math

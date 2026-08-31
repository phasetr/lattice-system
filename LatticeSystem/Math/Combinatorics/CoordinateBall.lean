/-
Coordinate sup-norm balls in `ℤ^d`.

For a finite site set `Λ` carrying injective integer coordinates `pos : Λ → (Fin d → ℤ)`, the
**coordinate sup-norm ball** `B_r(x) = {y ∈ Λ : ∀ i, |pos y i - pos x i| ≤ r}` has cardinality at
most `(2r+1)^d`. This is the `d`-dimensional analogue of the 1-D displacement-window count already
used at `Quantum/SpinS/LiebSchultzMattisGeneratorNorm.lean`: `card_siteBall_torusSupDist_le`
(`Quantum/SpinS/TorusSupDistance.lean`) recovers the *torus sup-distance ball count* from this
coordinate ball, transporting it via `pos y i := signedRingDisp L (x i) (y i)` and reusing
`card_coordSupBall_le` unchanged, at the radii `2r` and `4r` needed by Tasaki Problem 3.4.a. The
1-D window count `window_card_le` itself is *not* routed through that transport — it keeps its own
independent `card_le_card_of_injOn`-into-`Finset.Icc` proof, so the two counting arguments remain
near-duplicates at `d = 1`.

The sup-norm reading of Tasaki's unqualified `|x - y| ≤ r` is chosen because the Euclidean ball is
contained in the sup-norm ball: a locality hypothesis phrased on the sup-norm ball is the weaker
one, and in `ℤ^d` itself it is the reading under which a radius-`r` ball has exactly `(2r+1)^d`
sites. The transported torus count (`card_siteBall_torusSupDist_le`) only inherits this file's
`≤ (2r+1)^d` bound, not the equality — it is strictly smaller once the torus side length `L` is
below `2r+1`. The counts this file's transport delivers to Problem 3.4.a are at radii `2r` and
`4r`.

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

Instantiated (via `card_siteBall_torusSupDist_le`) at radius `2r` and at radius `4r`, this lemma
supplies the two counts the range-`r` capstone of Problem 3.4.a needs: `(4r+1)^d` and `(8r+1)^d`. -/
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

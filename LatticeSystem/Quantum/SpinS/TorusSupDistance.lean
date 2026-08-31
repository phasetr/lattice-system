/-
The sup-norm distance on the periodic lattice `Fin d → Fin L`.

Tasaki's `Λ_L` is the `d`-dimensional box with the periodic identification (p. 52), so the distance
entering a range-`r` locality premise is the *cyclic* one: coordinate-wise ring distance, combined
by the sup norm.  `torusSupDist` is that distance, and it is a genuine metric — symmetric, and
satisfying the triangle inequality — which is exactly what the ball-disjointness of
`Math/Combinatorics/SiteBall.lean` requires.

Its balls are counted by transporting them to coordinate balls: with the centre fixed, the map
`y ↦ (i ↦ δ(x i, y i))` built from the signed cyclic displacement is injective and turns the
sup-distance ball into a coordinate sup-norm ball, so `card_coordSupBall_le` applies unchanged and
gives the periodic count `(2r+1)^d`.  Reading Tasaki's unqualified `|x − y| ≤ r` in the sup norm is
the weaker locality hypothesis, since the Euclidean ball is contained in the sup-norm ball.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §2.1 p. 52 (periodic lattice), §3.4, Problem 3.4.a, statement pp. 67-68.
-/
import LatticeSystem.Quantum.SpinS.RingDistance
import LatticeSystem.Math.Combinatorics.SiteBall
import LatticeSystem.Math.Combinatorics.CoordinateBall

namespace LatticeSystem.Quantum

open LatticeSystem.Math

/-- The **torus sup-distance** on `Fin d → Fin L`: the largest of the `d` coordinate-wise ring
distances.  It is the periodic analogue of the sup norm on `ℤ^d`, and the distance in which
Tasaki's range-`r` locality premise is read. -/
def torusSupDist (d L : ℕ) (x y : Fin d → Fin L) : ℕ :=
  Finset.univ.sup fun i => ringDist L (x i) (y i)

/-- A sup-distance bound is exactly a coordinate-wise ring-distance bound. -/
theorem torusSupDist_le_iff {d L : ℕ} {x y : Fin d → Fin L} {r : ℕ} :
    torusSupDist d L x y ≤ r ↔ ∀ i, ringDist L (x i) (y i) ≤ r := by
  unfold torusSupDist
  constructor
  · intro h i
    exact le_trans (Finset.le_sup (f := fun i => ringDist L (x i) (y i)) (Finset.mem_univ i)) h
  · intro h
    exact Finset.sup_le fun i _ => h i

/-- The torus sup-distance is symmetric, coordinate-wise from `ringDist_comm`. -/
theorem torusSupDist_comm (d L : ℕ) (x y : Fin d → Fin L) :
    torusSupDist d L x y = torusSupDist d L y x := by
  unfold torusSupDist
  exact Finset.sup_congr rfl fun i _ => ringDist_comm L (x i) (y i)

/-- The torus sup-distance satisfies the triangle inequality: each coordinate obeys
`ringDist_triangle`, and each coordinate term is bounded by the corresponding sup. -/
theorem torusSupDist_triangle (d L : ℕ) (x y z : Fin d → Fin L) :
    torusSupDist d L x z ≤ torusSupDist d L x y + torusSupDist d L y z := by
  refine torusSupDist_le_iff.mpr fun i =>
    le_trans (ringDist_triangle L (x i) (y i) (z i)) (Nat.add_le_add ?_ ?_)
  · exact Finset.le_sup (f := fun i => ringDist L (x i) (y i)) (Finset.mem_univ i)
  · exact Finset.le_sup (f := fun i => ringDist L (y i) (z i)) (Finset.mem_univ i)

/-- **Periodic ball count**: `|B_r(x)| ≤ (2r+1)^d` for the torus sup-distance.  Centring the signed
cyclic displacement at `x` gives coordinates `pos y i = δ(x i, y i)` that are injective
(`signedRingDisp_injective`) and satisfy `|pos y i − pos x i| = ringDist L (x i) (y i)`, so the
sup-distance ball *is* the coordinate sup-norm ball of `card_coordSupBall_le` and inherits its
count.  No injectivity hypothesis is needed: periodicity supplies it. -/
theorem card_siteBall_torusSupDist_le (d L r : ℕ) (x : Fin d → Fin L) :
    (siteBall (torusSupDist d L) r x).card ≤ (2 * r + 1) ^ d := by
  classical
  set pos : (Fin d → Fin L) → (Fin d → ℤ) := fun y i => signedRingDisp L (x i) (y i) with hpos
  have hinj : Function.Injective pos := by
    intro y₁ y₂ h
    funext i
    exact signedRingDisp_injective L (x i) (congrFun h i)
  have hdisp : ∀ y : Fin d → Fin L, ∀ i,
      |pos y i - pos x i| = (ringDist L (x i) (y i) : ℤ) := by
    intro y i
    rw [hpos]
    simp only
    rw [signedRingDisp_self, sub_zero, Int.abs_eq_natAbs, natAbs_signedRingDisp_eq_ringDist]
  have hball : siteBall (torusSupDist d L) r x = coordSupBall pos r x := by
    ext y
    rw [mem_siteBall, mem_coordSupBall, torusSupDist_le_iff]
    constructor
    · intro h i
      rw [hdisp y i]
      exact_mod_cast (ringDist_comm L (y i) (x i) ▸ h i)
    · intro h i
      have hi := h i
      rw [hdisp y i] at hi
      rw [ringDist_comm]
      exact_mod_cast hi
  rw [hball]
  exact card_coordSupBall_le pos hinj r x

end LatticeSystem.Quantum

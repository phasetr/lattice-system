import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Cyclic geometry of the ring `Fin L`

The periodic-boundary distance between two sites of the ring `Fin L`, its signed refinement, and
the metric facts they satisfy: symmetry, vanishing on the diagonal, the triangle inequality, and
injectivity of the signed displacement seen from a fixed centre.

The module carries no operator-algebra dependencies, so every consumer of ring geometry can share
one definition: the locality predicate `IsLocalRangeR` and the centered local twist generator
(Tasaki §6.2), the correlation-decay estimates (Tasaki §6.3), and the periodic-lattice sup-distance
used by the range-`r` double-commutator bound (Tasaki §3.4, Problem 3.4.a).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, §6.2, §6.3.
-/

namespace LatticeSystem.Quantum

/-- The **ring distance** between sites `x, y` on `Fin L`: the shorter of the two cyclic arc lengths
`(y − x) mod L` and `(x − y) mod L`. -/
def ringDist (L : ℕ) (x y : Fin L) : ℕ :=
  min ((y.val + L - x.val) % L) ((x.val + L - y.val) % L)

/-- The ring distance is symmetric: it is the minimum of the two arc lengths, which the exchange of
`x` and `y` swaps. -/
theorem ringDist_comm (L : ℕ) (x y : Fin L) : ringDist L x y = ringDist L y x :=
  Nat.min_comm _ _

/-- The ring distance vanishes on the diagonal: both arcs from a site to itself have length
`L % L = 0`. -/
theorem ringDist_self (L : ℕ) (x : Fin L) : ringDist L x x = 0 := by
  have hx := x.isLt
  have harc : (x.val + L - x.val) % L = 0 := by
    have he : x.val + L - x.val = L := by omega
    rw [he, Nat.mod_self]
  unfold ringDist
  rw [harc]
  exact min_self 0

/-- The two arcs between `x` and `y` either partition the whole ring or are both degenerate: their
lengths sum to `L` unless `x = y`, in which case both vanish.  This is the case split the triangle
inequality reduces to. -/
private theorem ringArc_add_ringArc (L : ℕ) (x y : Fin L) :
    (y.val + L - x.val) % L + (x.val + L - y.val) % L = L ∨
      ((y.val + L - x.val) % L = 0 ∧ (x.val + L - y.val) % L = 0) := by
  have hx := x.isLt
  have hy := y.isLt
  rcases lt_trichotomy x.val y.val with h | h | h
  · left
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · right
    constructor
    · rw [h]; simp
    · rw [h]; simp
  · left
    rw [Nat.mod_eq_of_lt (show y.val + L - x.val < L by omega),
      Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- Forward arc lengths compose modulo `L`: going from `x` to `y` and then from `y` to `z` covers
the same forward arc as going from `x` to `z`. -/
private theorem ringArc_add (L : ℕ) (x y z : Fin L) :
    ((y.val + L - x.val) % L + (z.val + L - y.val) % L) % L = (z.val + L - x.val) % L := by
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  rw [← Nat.add_mod]
  have he : (y.val + L - x.val) + (z.val + L - y.val) = (z.val + L - x.val) + L := by omega
  rw [he, Nat.add_mod_right]

/-- The ring distance satisfies the triangle inequality, so it is a genuine metric on `Fin L`.  The
composed forward arc from `x` to `z` either is already reduced or overshoots by exactly one turn of
the ring, and in both cases the arc-pair identity bounds the minimum. -/
theorem ringDist_triangle (L : ℕ) (x y z : Fin L) :
    ringDist L x z ≤ ringDist L x y + ringDist L y z := by
  have hx := x.isLt
  have hL : 0 < L := by omega
  have h1 := ringArc_add_ringArc L x y
  have h2 := ringArc_add_ringArc L y z
  have h3 := ringArc_add_ringArc L x z
  have hsum := ringArc_add L x y z
  have hlt : ∀ a b : ℕ, (a + L - b) % L < L := fun a b => Nat.mod_lt _ hL
  have hcase : ((y.val + L - x.val) % L + (z.val + L - y.val) % L) % L
      = (y.val + L - x.val) % L + (z.val + L - y.val) % L ∨
      ((y.val + L - x.val) % L + (z.val + L - y.val) % L) % L + L
      = (y.val + L - x.val) % L + (z.val + L - y.val) % L := by
    by_cases hlt' : (y.val + L - x.val) % L + (z.val + L - y.val) % L < L
    · exact Or.inl (Nat.mod_eq_of_lt hlt')
    · right
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by
        have := hlt y.val x.val
        have := hlt z.val y.val
        omega)]
      omega
  have ha := hlt y.val x.val
  have hb := hlt z.val y.val
  have hc := hlt z.val x.val
  have hd := hlt x.val z.val
  have he := hlt x.val y.val
  have hf := hlt y.val z.val
  unfold ringDist
  omega

/-- The **signed cyclic displacement** `δ(x,y)` from `x` to `y` on the ring `Fin L`: the shorter
cyclic arc length taken with a `+` sign when the forward arc `(y − x) mod L` is the shorter one and
a `−` sign otherwise, so that `|δ(x,y)| = ringDist L x y`.  It gives the ring-distance-centered
twist angle `(2π/L)·δ(x,y)` of `y` relative to `x` (Tasaki eq. (6.2.27)), free of the `2π` seam jump
of the raw linear angle `θ_y = 2π(y+1)/L` for windows that wrap around the periodic boundary. -/
def signedRingDisp (L : ℕ) (x y : Fin L) : ℤ :=
  if (y.val + L - x.val) % L ≤ (x.val + L - y.val) % L
    then (((y.val + L - x.val) % L : ℕ) : ℤ)
    else -(((x.val + L - y.val) % L : ℕ) : ℤ)

/-- The signed cyclic displacement has absolute value equal to the ring distance,
`|δ(x,y)| = ringDist L x y` (Tasaki §6.2): the sign only records the shorter-arc direction while the
magnitude is the ring distance itself.  It converts a ring-distance bound into the integer-interval
bound used by the ring-window and torus-ball cardinality counts. -/
theorem natAbs_signedRingDisp_eq_ringDist (L : ℕ) (x y : Fin L) :
    (signedRingDisp L x y).natAbs = ringDist L x y := by
  unfold signedRingDisp ringDist
  split_ifs with h <;> omega

/-- The signed ring displacement `δ(x,y)` is congruent to the raw index gap `y − x` modulo `L`:
their difference is divisible by `L`.  This captures the periodic-seam winding by which the linear
LSM angle `θ_y = 2π(y+1)/L` differs from the ring-centered angle `(2π/L) δ(x,y)`. -/
theorem dvd_sub_signedRingDisp (L : ℕ) (x y : Fin L) :
    (L : ℤ) ∣ ((y.val : ℤ) - (x.val : ℤ) - signedRingDisp L x y) := by
  have hx := x.isLt
  have hy := y.isLt
  have key : (signedRingDisp L x y : ℤ) ≡ (y.val : ℤ) - (x.val : ℤ) [ZMOD (L : ℤ)] := by
    have hxL : x.val ≤ y.val + L := by omega
    have hyL : y.val ≤ x.val + L := by omega
    unfold signedRingDisp
    split_ifs with h
    · calc (((y.val + L - x.val) % L : ℕ) : ℤ)
          = ((y.val + L - x.val : ℕ) : ℤ) % (L : ℤ) := by rw [Int.natCast_mod]
        _ ≡ ((y.val + L - x.val : ℕ) : ℤ) [ZMOD (L : ℤ)] := Int.mod_modEq _ _
        _ = (y.val : ℤ) + (L : ℤ) - (x.val : ℤ) := by rw [Nat.cast_sub hxL]; push_cast; ring
        _ ≡ (y.val : ℤ) - (x.val : ℤ) [ZMOD (L : ℤ)] := Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    · calc (-(((x.val + L - y.val) % L : ℕ) : ℤ))
          = -(((x.val + L - y.val : ℕ) : ℤ) % (L : ℤ)) := by rw [Int.natCast_mod]
        _ ≡ -(((x.val + L - y.val : ℕ) : ℤ)) [ZMOD (L : ℤ)] := (Int.mod_modEq _ _).neg
        _ = -((x.val : ℤ) + (L : ℤ) - (y.val : ℤ)) := by rw [Nat.cast_sub hyL]; push_cast; ring
        _ ≡ (y.val : ℤ) - (x.val : ℤ) [ZMOD (L : ℤ)] := Int.modEq_iff_dvd.mpr ⟨1, by ring⟩
  exact Int.modEq_iff_dvd.mp key

/-- The signed cyclic displacement vanishes on the diagonal, matching `ringDist_self` with a
sign. -/
theorem signedRingDisp_self (L : ℕ) (x : Fin L) : signedRingDisp L x x = 0 := by
  have hx := x.isLt
  have harc : (x.val + L - x.val) % L = 0 := by
    have he : x.val + L - x.val = L := by omega
    rw [he, Nat.mod_self]
  unfold signedRingDisp
  rw [harc]
  simp

/-- Seen from a fixed centre `x`, the signed cyclic displacement `y ↦ δ(x,y)` is **injective**: two
sites with the same displacement have indices congruent modulo `L`, hence are equal in `Fin L`.
This is what lets a ring window, or a torus sup-distance ball, be counted inside an integer
interval. -/
theorem signedRingDisp_injective (L : ℕ) (x : Fin L) :
    Function.Injective (signedRingDisp L x) := by
  intro y₁ y₂ heq
  have hd1 := dvd_sub_signedRingDisp L x y₁
  have hd2 := dvd_sub_signedRingDisp L x y₂
  rw [heq] at hd1
  have hdvd : (L : ℤ) ∣ ((y₁.val : ℤ) - (y₂.val : ℤ)) := by
    have hs := dvd_sub hd1 hd2
    have hcalc : ((y₁.val : ℤ) - x.val - signedRingDisp L x y₂)
        - ((y₂.val : ℤ) - x.val - signedRingDisp L x y₂) = (y₁.val : ℤ) - (y₂.val : ℤ) := by ring
    rwa [hcalc] at hs
  have h1 : (y₁.val : ℤ) < L := by exact_mod_cast y₁.isLt
  have h2 : (y₂.val : ℤ) < L := by exact_mod_cast y₂.isLt
  have hzero : (y₁.val : ℤ) - (y₂.val : ℤ) = 0 := by
    by_contra hne
    have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hne
    omega
  exact Fin.ext (by omega)

end LatticeSystem.Quantum

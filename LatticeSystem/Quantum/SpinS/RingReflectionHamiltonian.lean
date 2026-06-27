/-
The chain Hamiltonian and staggered order operator under the ring reflection map `θ`
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 2).

Building on `RingReflectionTheta.lean`, this file computes the `θ`-images of the staggered order
operator and the staggered-field chain Hamiltonian.  The two key geometric facts are the
orientation-reversal of the directed ring coupling under reflection and the staggered-sign flip.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionTheta

namespace LatticeSystem.Quantum

/-- **Orientation reversal of the ring coupling under bond reflection**:
`J (r x) (r y) = J y x`.  The bond reflection `r(x) = 2n − 1 − x` reverses the cyclic orientation,
so the directed nearest-neighbor edge `x → x+1` maps to the reversed edge. -/
theorem ringCoupling_ringReflect (n : ℕ) (hn : 1 ≤ n) (x y : Fin (2 * n)) :
    ringCoupling (2 * n) (ringReflect n x) (ringReflect n y) = ringCoupling (2 * n) y x := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [ringCoupling, ringReflect_val]
  have hxmod : (2 * n - 1 - x.val + 1) % (2 * n) = if x.val = 0 then 0 else 2 * n - x.val := by
    rcases eq_or_ne x.val 0 with hx0 | hx0
    · rw [if_pos hx0, hx0, show 2 * n - 1 - 0 + 1 = 2 * n by omega, Nat.mod_self]
    · rw [if_neg hx0, show 2 * n - 1 - x.val + 1 = 2 * n - x.val by omega,
        Nat.mod_eq_of_lt (by omega)]
  have hymod : (y.val + 1) % (2 * n) = if y.val = 2 * n - 1 then 0 else y.val + 1 := by
    rcases eq_or_ne y.val (2 * n - 1) with hy1 | hy1
    · rw [if_pos hy1, hy1, show 2 * n - 1 + 1 = 2 * n by omega, Nat.mod_self]
    · rw [if_neg hy1, Nat.mod_eq_of_lt (by omega)]
  have key : (2 * n - 1 - y.val = (2 * n - 1 - x.val + 1) % (2 * n))
      ↔ (x.val = (y.val + 1) % (2 * n)) := by
    rw [hxmod, hymod]
    split_ifs <;> omega
  simp only [key]

end LatticeSystem.Quantum

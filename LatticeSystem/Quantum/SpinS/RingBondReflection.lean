/-
Even-ring bond reflection geometry (foundation for Tasaki §4.1 Theorem 4.2, Shastry's 1D no-SSB).

Reflection positivity for the one-dimensional ring of `L = 2n` sites uses the **bond reflection**
`r(x) = 2n − 1 − x`, the reflection across the two opposite bonds `(n−1, n)` and `(2n−1, 0)`.  It is an
involution that swaps the left half `{0, …, n−1}` and the right half `{n, …, 2n−1}`, preserves the
nearest-neighbor adjacency of the ring, and flips the staggered (`(−1)^x`) sublattice sign.  This file
establishes that geometry; later layers build the reflection map `θ`, the Hamiltonian decomposition,
Gaussian domination, the infrared bound, and finally Shastry's estimate.
-/
import LatticeSystem.Quantum.SpinS.ShastryNoSSB

namespace LatticeSystem.Quantum

/-- The **bond reflection** of the even ring `Fin (2n)`: `r(x) = 2n − 1 − x`.  Reflection across the
midpoints of the two opposite bonds `(n−1, n)` and `(2n−1, 0)`. -/
def ringReflect (n : ℕ) (x : Fin (2 * n)) : Fin (2 * n) :=
  ⟨2 * n - 1 - x.val, by omega⟩

@[simp] theorem ringReflect_val (n : ℕ) (x : Fin (2 * n)) :
    (ringReflect n x).val = 2 * n - 1 - x.val := rfl

/-- The bond reflection is an involution. -/
theorem ringReflect_involutive (n : ℕ) : Function.Involutive (ringReflect n) := by
  intro x
  apply Fin.ext
  simp only [ringReflect_val]
  omega

/-- The bond reflection is a bijection. -/
theorem ringReflect_bijective (n : ℕ) : Function.Bijective (ringReflect n) :=
  (ringReflect_involutive n).bijective

/-- The bond reflection swaps the left half `{0, …, n−1}` and the right half `{n, …, 2n−1}`:
`x` lies in the left half iff `r(x)` lies in the right half. -/
theorem ringReflect_lt_iff (n : ℕ) (x : Fin (2 * n)) :
    (ringReflect n x).val < n ↔ n ≤ x.val := by
  simp only [ringReflect_val]
  omega

/-- The bond reflection **flips the staggered sublattice sign**: `ε_{r(x)} = −ε_x`, i.e. `r` maps
the even sublattice to the odd one and vice versa (`2n − 1` is odd). -/
theorem ringStaggeredSublattice_ringReflect (n : ℕ) (x : Fin (2 * n)) :
    ringStaggeredSublattice (2 * n) (ringReflect n x) = !(ringStaggeredSublattice (2 * n) x) := by
  simp only [ringStaggeredSublattice, ringReflect_val]
  have hx : x.val < 2 * n := x.isLt
  by_cases h : x.val % 2 = 0
  · simp only [h, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
  · simp only [h, decide_false, Bool.not_false, decide_eq_true_eq]; omega

end LatticeSystem.Quantum

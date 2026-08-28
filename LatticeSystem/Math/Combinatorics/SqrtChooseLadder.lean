/-
Square-root binomial weights of a spin ladder step.

A spin ladder operator carries the matrix element `√((t+1)(n−t))` between the two basis states
indexed by `t` and `t+1`, while the states themselves carry the Clebsch–Gordan weights
`√(binom n ·)`.  This file proves the two ways of absorbing such a matrix element into a
neighbouring weight — attaching it to `√(binom n t)` (`sqrt_raise_coeff`) or to
`√(binom n (t+1))` (`sqrt_lower_coeff`) — together with the arithmetic core they share,
`sqrt_choose_step`, the `√`-form of `Nat.choose_succ_right_eq`.

Which of the two a given ladder step needs is fixed by whether the state being acted on is
indexed by `t` or by `t+1`, not by the direction of the step, so consumers that index basis
states oppositely (the per-site Weyl transport of `Ŝ^±`, the one-site amplitudes of the
saturated-ferromagnet coherent state) exchange the roles of the two identities.
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Sqrt

namespace LatticeSystem.Math

/-- **The single arithmetic fact behind both ladders.**  The `√`-form of
`Nat.choose_succ_right_eq` (`binom(n,t+1)·(t+1) = binom(n,t)·(n−t)`): the Clebsch–Gordan weights
`√(binom(n,·))` of neighbouring basis states are related by the ladder matrix elements `√(t+1)`
and `√(n−t)`.  No hypothesis `t < n` is needed: above the top both sides vanish. -/
theorem sqrt_choose_step (n t : ℕ) :
    Real.sqrt (n.choose (t + 1)) * Real.sqrt ((t : ℝ) + 1)
      = Real.sqrt (n.choose t) * Real.sqrt ((n - t : ℕ) : ℝ) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  congr 1
  exact_mod_cast Nat.choose_succ_right_eq n t

/-- **Ladder element absorbed into the lower weight.**  The ladder matrix element `√((t+1)(n−t))`
times the weight `√(binom(n,t))` of the state indexed by `t` equals the weight `√(binom(n,t+1))`
of the neighbouring state times `t+1`.  The real subtraction `(n:ℝ) − (t+1) + 1`, in which the
matrix elements of `spinSOpPlus`/`spinSOpMinus` are stated, is bridged to the truncated `n − t`
by `t < n`. -/
theorem sqrt_raise_coeff {n t : ℕ} (ht : t < n) :
    Real.sqrt (((t : ℝ) + 1) * ((n : ℝ) - ((t : ℝ) + 1) + 1)) * Real.sqrt (n.choose t)
      = Real.sqrt (n.choose (t + 1)) * ((t : ℝ) + 1) := by
  have hcast : (n : ℝ) - ((t : ℝ) + 1) + 1 = ((n - t : ℕ) : ℝ) := by
    rw [Nat.cast_sub ht.le]
    ring
  have hsq : Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) = (t : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  rw [hcast, Real.sqrt_mul (by positivity)]
  calc Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((n - t : ℕ) : ℝ) * Real.sqrt (n.choose t)
      = Real.sqrt (n.choose t) * Real.sqrt ((n - t : ℕ) : ℝ) * Real.sqrt ((t : ℝ) + 1) := by ring
    _ = Real.sqrt (n.choose (t + 1)) * Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) := by
        rw [sqrt_choose_step]
    _ = Real.sqrt (n.choose (t + 1)) * ((t : ℝ) + 1) := by rw [mul_assoc, hsq]

/-- **Ladder element absorbed into the upper weight.**  The ladder matrix element `√((n−t)(t+1))`
times the weight `√(binom(n,t+1))` of the state indexed by `t+1` equals the weight `√(binom(n,t))`
of the neighbouring state times `n − t`.  Companion of `sqrt_raise_coeff`: the two differ only in
which of the two neighbouring weights the matrix element is attached to. -/
theorem sqrt_lower_coeff {n t : ℕ} (ht : t < n) :
    Real.sqrt (((n : ℝ) - (t : ℝ)) * ((t : ℝ) + 1)) * Real.sqrt (n.choose (t + 1))
      = Real.sqrt (n.choose t) * ((n - t : ℕ) : ℝ) := by
  have hcast : (n : ℝ) - (t : ℝ) = ((n - t : ℕ) : ℝ) := (Nat.cast_sub ht.le).symm
  have hsq : Real.sqrt ((n - t : ℕ) : ℝ) * Real.sqrt ((n - t : ℕ) : ℝ) = ((n - t : ℕ) : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [hcast, Real.sqrt_mul (Nat.cast_nonneg _)]
  calc Real.sqrt ((n - t : ℕ) : ℝ) * Real.sqrt ((t : ℝ) + 1) * Real.sqrt (n.choose (t + 1))
      = Real.sqrt (n.choose (t + 1)) * Real.sqrt ((t : ℝ) + 1)
          * Real.sqrt ((n - t : ℕ) : ℝ) := by ring
    _ = Real.sqrt (n.choose t) * Real.sqrt ((n - t : ℕ) : ℝ)
          * Real.sqrt ((n - t : ℕ) : ℝ) := by rw [sqrt_choose_step]
    _ = Real.sqrt (n.choose t) * ((n - t : ℕ) : ℝ) := by rw [mul_assoc, hsq]

end LatticeSystem.Math

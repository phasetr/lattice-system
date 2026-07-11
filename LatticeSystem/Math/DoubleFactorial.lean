/-
Double-factorial arithmetic for the even factorial.

This file proves the elementary identity `(2a)! = 2^a · a! · (2a-1)‼` splitting an even factorial
into its even and odd double-factorial parts.  It is a thin corollary of the mathlib lemmas
`Nat.doubleFactorial_two_mul` (`(2n)‼ = 2^n · n!`) and `Nat.factorial_eq_mul_doubleFactorial`
(`(n+1)! = (n+1)‼ · n‼`), and feeds the Prop 4.10 (Tasaki §4.2.2, p. 108) coefficient match, where
the per-configuration even factorials `(2 hᵢ)!` are converted into the odd double factorials
`(2 hᵢ - 1)‼` appearing in the sphere-moment closed form.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §4.2.2, p. 108.
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial

namespace LatticeSystem.Math

open scoped Nat

/-- **Even factorial split**: `(2a)! = 2^a · a! · (2a-1)‼`.

For `a = 0` both sides are `1` (using `Nat.doubleFactorial` at the truncated argument `2·0-1 = 0`,
with `0‼ = 1`).  For `a = n+1` the even part `(2a)‼ = 2^a · a!` comes from
`Nat.doubleFactorial_two_mul` and the factorial-to-double-factorial recursion
`Nat.factorial_eq_mul_doubleFactorial` at `2n+1` supplies the odd double factorial. -/
theorem two_mul_factorial_eq (a : ℕ) : (2 * a)! = 2 ^ a * a ! * (2 * a - 1)‼ := by
  cases a with
  | zero => decide
  | succ n =>
    have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    have h2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [h1, Nat.factorial_eq_mul_doubleFactorial (2 * n + 1), ← h1,
      Nat.doubleFactorial_two_mul (n + 1), h2]

end LatticeSystem.Math

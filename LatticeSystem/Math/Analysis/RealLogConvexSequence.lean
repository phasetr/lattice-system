import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Log-convexity telescoping for a nonnegative real sequence

Source-independent real-sequence backbone behind the Cauchy–Schwarz moment inequalities of the
Anderson tower (Tasaki §4.2).  For a nonnegative sequence `m : ℕ → ℝ` whose consecutive triples are
log-convex (`m (k+1)² ≤ m k · m (k+2)`) we derive:

* `real_logConvex_cross` — the cross monotonicity `m 1 · m n ≤ m 0 · m (n+1)` (the ratio
  `m (n+1) / m n` is non-decreasing);
* `real_logConvex_geom` — its geometric iterate `m 1 ^ (n+1) ≤ m 0 ^ n · m (n+1)`;
* `real_logConvex_geometric_lower` — once a base ratio bound `r · m 0 ≤ m 1` is supplied (with
  `0 ≤ r` and `0 < m 0`), the telescoped lower bound `r ^ (n+1) · m 0 ≤ m (n+1)`.

These are the abstract kernels shared by the `p̂`-moment bounds
(`phatMoment_cross` / `phatMoment_geom_le` / `phatMoment_ge_of_lro`) and the squared-order-operator
moment bounds of Proposition 4.10 (`orderSqMoment_ge`); the concrete Hermitian Cauchy–Schwarz inputs
supplying `hsq` live in the respective quantum modules.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1–§4.2.2, eqs. (4.2.35)–(4.2.37), pp. 104–106.
-/

namespace LatticeSystem.Math

/-- **Cross log-convexity of a nonnegative log-convex sequence**: if `0 ≤ m k` for all `k` and
`m (k+1)² ≤ m k · m (k+2)`, then `m 1 · m n ≤ m 0 · m (n+1)`, i.e. the ratio `m (n+1) / m n` is
non-decreasing.  This is the abstract form of eq. (4.2.36). -/
theorem real_logConvex_cross {m : ℕ → ℝ} (hnn : ∀ k, 0 ≤ m k)
    (hsq : ∀ k, m (k + 1) ^ 2 ≤ m k * m (k + 2)) (n : ℕ) :
    m 1 * m n ≤ m 0 * m (n + 1) := by
  induction n with
  | zero => exact le_of_eq (mul_comm _ _)
  | succ k ih =>
    have hsqk : m (k + 1) ^ 2 ≤ m k * m (k + 2) := hsq k
    rcases eq_or_lt_of_le (hnn k) with h0 | hpos
    · have hle : m (k + 1) ^ 2 ≤ 0 := by rw [← h0, zero_mul] at hsqk; exact hsqk
      have hk1 : m (k + 1) = 0 :=
        pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hle (sq_nonneg _))
      rw [hk1, mul_zero]
      exact mul_nonneg (hnn 0) (hnn (k + 1 + 1))
    · have key : m k * (m 1 * m (k + 1)) ≤ m k * (m 0 * m (k + 2)) :=
        calc m k * (m 1 * m (k + 1)) = m 1 * m k * m (k + 1) := by ring
          _ ≤ m 0 * m (k + 1) * m (k + 1) := mul_le_mul_of_nonneg_right ih (hnn (k + 1))
          _ = m 0 * m (k + 1) ^ 2 := by ring
          _ ≤ m 0 * (m k * m (k + 2)) := mul_le_mul_of_nonneg_left hsqk (hnn 0)
          _ = m k * (m 0 * m (k + 2)) := by ring
      exact le_of_mul_le_mul_left key hpos

/-- **Geometric lower bound** for a nonnegative log-convex sequence:
`m 1 ^ (n+1) ≤ m 0 ^ n · m (n+1)` (iterating `real_logConvex_cross`).  The abstract form of the
telescoped eq. (4.2.36). -/
theorem real_logConvex_geom {m : ℕ → ℝ} (hnn : ∀ k, 0 ≤ m k)
    (hsq : ∀ k, m (k + 1) ^ 2 ≤ m k * m (k + 2)) (n : ℕ) :
    m 1 ^ (n + 1) ≤ m 0 ^ n * m (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc m 1 ^ (k + 2) = m 1 ^ (k + 1) * m 1 := by ring
      _ ≤ (m 0 ^ k * m (k + 1)) * m 1 := mul_le_mul_of_nonneg_right ih (hnn 1)
      _ = m 0 ^ k * (m 1 * m (k + 1)) := by ring
      _ ≤ m 0 ^ k * (m 0 * m (k + 2)) :=
          mul_le_mul_of_nonneg_left (real_logConvex_cross hnn hsq (k + 1)) (pow_nonneg (hnn 0) k)
      _ = m 0 ^ (k + 1) * m (k + 2) := by ring

/-- **Telescoped geometric lower bound under a base ratio bound** (eq. (4.2.37)): if the sequence is
nonnegative and log-convex, `0 ≤ r`, `0 < m 0`, and the base bound `r · m 0 ≤ m 1` holds, then
`r ^ (n+1) · m 0 ≤ m (n+1)` for every `n` (the normalized moment `m (n+1) / m 0 ≥ r ^ (n+1)`). -/
theorem real_logConvex_geometric_lower {m : ℕ → ℝ} (hnn : ∀ k, 0 ≤ m k)
    (hsq : ∀ k, m (k + 1) ^ 2 ≤ m k * m (k + 2)) {r : ℝ} (hr : 0 ≤ r) (hm0 : 0 < m 0)
    (hbase : r * m 0 ≤ m 1) (n : ℕ) :
    r ^ (n + 1) * m 0 ≤ m (n + 1) := by
  have hgeom := real_logConvex_geom hnn hsq n
  have hpow : (r * m 0) ^ (n + 1) ≤ m 1 ^ (n + 1) :=
    pow_le_pow_left₀ (mul_nonneg hr hm0.le) hbase (n + 1)
  have hkey : r ^ (n + 1) * m 0 ^ (n + 1) ≤ m 0 ^ n * m (n + 1) := by
    calc r ^ (n + 1) * m 0 ^ (n + 1)
          = (r * m 0) ^ (n + 1) := (mul_pow r (m 0) (n + 1)).symm
      _ ≤ m 1 ^ (n + 1) := hpow
      _ ≤ m 0 ^ n * m (n + 1) := hgeom
  have hfinal : m 0 ^ n * (r ^ (n + 1) * m 0) ≤ m 0 ^ n * m (n + 1) := by
    calc m 0 ^ n * (r ^ (n + 1) * m 0)
          = r ^ (n + 1) * m 0 ^ (n + 1) := by rw [pow_succ]; ring
      _ ≤ m 0 ^ n * m (n + 1) := hkey
  exact le_of_mul_le_mul_left hfinal (pow_pos hm0 n)

end LatticeSystem.Math

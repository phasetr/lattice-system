/-
Generic commutator power-telescoping identities in an associative (noncommutative) ring.

For a ring `R` and `H, A : R`, the single commutator of a power expands as a telescoping sum
`[H, Aᴹ] = Σ_{j<M} Aʲ [H, A] A^{M-1-j}` (`commutator_pow_eq_sum`), and its mirror
`[Aᴹ, X] = Σ_{j<M} Aʲ [A, X] A^{M-1-j}` (`commutator_pow_eq_sum'`).  Applying these twice yields the
**double** telescoping identity `[Aᴹ, [H, Aᴹ]] = Σ_{j,l<M} A^{j+l} [A, [H, A]] A^{2(M-1)-j-l}`
(`double_commutator_pow_eq_double_sum`): the `M²` insertion positions of the single physical double
commutator `d̃ = [A, [H, A]]` between powers of `A`.

This is the generic algebra behind Tasaki's Anderson-tower numerator identity (eq. (4.2.71) in Hal
Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §4.2.2,
p. 112), pulled out here as a source-agnostic ring lemma.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

namespace LatticeSystem

/-- **Commutator power telescope** `[H, Aᴹ] = Σ_{j<M} Aʲ [H, A] A^{M-1-j}` in any ring. -/
theorem commutator_pow_eq_sum {R : Type*} [Ring R] (H A : R) (M : ℕ) :
    H * A ^ M - A ^ M * H
      = ∑ j ∈ Finset.range M, A ^ j * (H * A - A * H) * A ^ (M - 1 - j) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hsplit : H * A ^ (m + 1) - A ^ (m + 1) * H
        = (H * A ^ m - A ^ m * H) * A + A ^ m * (H * A - A * H) := by
      rw [pow_succ]; noncomm_ring
    rw [hsplit, ih, Finset.sum_mul,
      show A ^ (m + 1 - 1 - m) = (1 : R) by simp, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [mul_assoc, ← pow_succ]
    congr 2
    omega

/-- **Mirror commutator power telescope** `[Aᴹ, X] = Σ_{j<M} Aʲ [A, X] A^{M-1-j}` in any ring (the
outer power on the left, needed for the second telescoping in the double commutator). -/
theorem commutator_pow_eq_sum' {R : Type*} [Ring R] (X A : R) (M : ℕ) :
    A ^ M * X - X * A ^ M
      = ∑ j ∈ Finset.range M, A ^ j * (A * X - X * A) * A ^ (M - 1 - j) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hsplit : A ^ (m + 1) * X - X * A ^ (m + 1)
        = (A ^ m * X - X * A ^ m) * A + A ^ m * (A * X - X * A) := by
      rw [pow_succ]; noncomm_ring
    rw [hsplit, ih, Finset.sum_mul,
      show A ^ (m + 1 - 1 - m) = (1 : R) by simp, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [mul_assoc, ← pow_succ]
    congr 2
    omega

/-- **Bracketed commutator power telescope** `[A, [H, Aᴹ]] = Σ_{j<M} Aʲ d̃ A^{M-1-j}` with the
single physical double commutator `d̃ = [A, [H, A]] = A (H A − A H) − (H A − A H) A`.  Obtained
from `commutator_pow_eq_sum` by distributing the outer `[A, ·]` across the telescoping sum. -/
theorem commutator_pow_bracket_eq_sum {R : Type*} [Ring R] (H A : R) (M : ℕ) :
    A * (H * A ^ M - A ^ M * H) - (H * A ^ M - A ^ M * H) * A
      = ∑ j ∈ Finset.range M,
          A ^ j * (A * (H * A - A * H) - (H * A - A * H) * A) * A ^ (M - 1 - j) := by
  rw [commutator_pow_eq_sum H A M, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hL : A * A ^ j = A ^ j * A := ((Commute.refl A).pow_right j).eq
  have hR : A ^ (M - 1 - j) * A = A * A ^ (M - 1 - j) :=
    (((Commute.refl A).pow_right (M - 1 - j)).eq).symm
  rw [show A * (A ^ j * (H * A - A * H) * A ^ (M - 1 - j))
        = A * A ^ j * (H * A - A * H) * A ^ (M - 1 - j) from by noncomm_ring, hL,
    show A ^ j * (H * A - A * H) * A ^ (M - 1 - j) * A
        = A ^ j * (H * A - A * H) * (A ^ (M - 1 - j) * A) from by noncomm_ring, hR]
  noncomm_ring

/-- **Double commutator power telescope** (Tasaki eq. (4.2.71)): the double commutator of a power
`[Aᴹ, [H, Aᴹ]]` is the `M²`-fold sum, over insertion positions `j, l < M`, of the single physical
double commutator `d̃ = [A, [H, A]]` sandwiched between powers of `A`,
`[Aᴹ, [H, Aᴹ]] = Σ_{j,l<M} A^{j+l} d̃ A^{2(M-1)-j-l}`.  Proved by telescoping the outer power with
`commutator_pow_eq_sum'` and each resulting inner bracket with `commutator_pow_bracket_eq_sum`. -/
theorem double_commutator_pow_eq_double_sum {R : Type*} [Ring R] (A H : R) (M : ℕ) :
    A ^ M * (H * A ^ M - A ^ M * H) - (H * A ^ M - A ^ M * H) * A ^ M
      = ∑ j ∈ Finset.range M, ∑ l ∈ Finset.range M,
          A ^ (j + l) * (A * (H * A - A * H) - (H * A - A * H) * A)
            * A ^ (2 * (M - 1) - j - l) := by
  rw [commutator_pow_eq_sum' (H * A ^ M - A ^ M * H) A M]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [commutator_pow_bracket_eq_sum H A M, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hl
  rw [show A ^ j
        * (A ^ l * (A * (H * A - A * H) - (H * A - A * H) * A) * A ^ (M - 1 - l))
        * A ^ (M - 1 - j)
        = (A ^ j * A ^ l) * (A * (H * A - A * H) - (H * A - A * H) * A)
          * (A ^ (M - 1 - l) * A ^ (M - 1 - j)) from by noncomm_ring,
    ← pow_add, ← pow_add,
    show (M - 1 - l) + (M - 1 - j) = 2 * (M - 1) - j - l from by omega]

end LatticeSystem

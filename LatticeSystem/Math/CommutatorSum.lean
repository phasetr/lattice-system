/-
Distributing a commutator over a finite sum, in an arbitrary ring.

For a ring `R` and a finite family `f : ι → R`, the commutator with a finite sum expands term by
term, `[A, Σ_{i∈s} f i] = Σ_{i∈s} [A, f i]` (`commutator_sum_right`) and its mirror
`[Σ_{i∈s} f i, A] = Σ_{i∈s} [f i, A]` (`commutator_sum_left`).  The scalar-weighted companions
`commutator_sum_smul_right` / `commutator_sum_smul_left` pull the coefficients of a `K`-algebra
out of the resulting sum.

These are the single home of the commutator-distribution argument: it is consumed both by the
staggered-order double-commutator expansion (Tasaki §4.1) and by the localised commutator identities
of Tasaki §3.4, eqs. (3.4.9)-(3.4.10) (H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, 1st ed., Springer 2020, pp. 66-67).
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Basic

namespace LatticeSystem

/-- **Commutator distributes over a finite sum on the right**: `[A, Σ_{i∈s} f i] = Σ_{i∈s} [A, f i]`
in any (non-unital, non-associative) ring. -/
theorem commutator_sum_right {R ι : Type*} [NonUnitalNonAssocRing R]
    (s : Finset ι) (A : R) (f : ι → R) :
    A * (∑ i ∈ s, f i) - (∑ i ∈ s, f i) * A = ∑ i ∈ s, (A * f i - f i * A) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- **Commutator distributes over a finite sum on the left**: `[Σ_{i∈s} f i, A] = Σ_{i∈s} [f i, A]`
in any (non-unital, non-associative) ring. -/
theorem commutator_sum_left {R ι : Type*} [NonUnitalNonAssocRing R]
    (s : Finset ι) (A : R) (f : ι → R) :
    (∑ i ∈ s, f i) * A - A * (∑ i ∈ s, f i) = ∑ i ∈ s, (f i * A - A * f i) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- **Commutator distributes over a scalar-weighted finite sum on the right**:
`[A, Σ_{i∈s} c i • B i] = Σ_{i∈s} c i • [A, B i]` in a `K`-algebra. -/
theorem commutator_sum_smul_right {K R ι : Type*} [CommSemiring K] [Ring R] [Algebra K R]
    (s : Finset ι) (A : R) (c : ι → K) (B : ι → R) :
    A * (∑ i ∈ s, c i • B i) - (∑ i ∈ s, c i • B i) * A
      = ∑ i ∈ s, c i • (A * B i - B i * A) := by
  rw [commutator_sum_right s A fun i => c i • B i]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, smul_mul_assoc, smul_sub]

/-- **Commutator distributes over a scalar-weighted finite sum on the left**:
`[Σ_{i∈s} c i • B i, A] = Σ_{i∈s} c i • [B i, A]` in a `K`-algebra. -/
theorem commutator_sum_smul_left {K R ι : Type*} [CommSemiring K] [Ring R] [Algebra K R]
    (s : Finset ι) (A : R) (c : ι → K) (B : ι → R) :
    (∑ i ∈ s, c i • B i) * A - A * (∑ i ∈ s, c i • B i)
      = ∑ i ∈ s, c i • (B i * A - A * B i) := by
  rw [commutator_sum_left s A fun i => c i • B i]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc, mul_smul_comm, smul_sub]

end LatticeSystem

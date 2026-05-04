import LatticeSystem.Fermion.CCDaggerIdempotent

/-!
# Power identities for the single-mode fermion idempotent projections

For every `k : ℕ` the two complementary single-mode idempotent
projections satisfy

  `n^(k+1)        = n`,
  `(c · c†)^(k+1) = c · c†`.

Both are immediate inductions starting from the squared identities:

- `n² = n` (`fermionNumber_sq`, `Mode.lean`).
- `(c · c†)² = c · c†`
  (`fermionAnnihilation_mul_fermionCreation_sq`, PR #974).

The result is the polynomial functional calculus on each of the
two rank-one projectors: any non-zero polynomial in `n` collapses
to a linear combination of `1` and `n` (constant plus rank-one
shift), and similarly for `c · c†`. Useful for spectral
computations and matrix-exponential expansions.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `n^(k+1) = n` for every `k : ℕ` (idempotent projection). -/
theorem fermionNumber_pow_succ (k : ℕ) :
    fermionNumber ^ (k + 1) = fermionNumber := by
  induction k with
  | zero => exact pow_one _
  | succ n ih =>
    rw [pow_succ, ih, fermionNumber_sq]

/-- `(c · c†)^(k+1) = c · c†` for every `k : ℕ` (idempotent
projection). -/
theorem fermionAnnihilation_mul_fermionCreation_pow_succ (k : ℕ) :
    (fermionAnnihilation * fermionCreation) ^ (k + 1) =
      fermionAnnihilation * fermionCreation := by
  induction k with
  | zero => exact pow_one _
  | succ n ih =>
    rw [pow_succ, ih, fermionAnnihilation_mul_fermionCreation_sq]

end LatticeSystem.Fermion

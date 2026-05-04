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

These power identities are the building blocks for collapsing
arbitrary positive-degree polynomials in `n` (or `c · c†`) into
the basis `{1, n}` (resp. `{1, c · c†}`); that linear collapse
itself is not proved here.

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

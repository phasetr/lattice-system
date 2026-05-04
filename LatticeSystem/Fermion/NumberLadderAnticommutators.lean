import LatticeSystem.Fermion.AnnihilationNumberIdentities
import LatticeSystem.Fermion.CreationNumberIdentities

/-!
# Fermion ladder anticommutators `{n, c} = c` and `{n, c†} = c†`

For the single-mode fermion the number operator `n` and the
ladder operators `c`, `c†` satisfy the anticommutator identities

  `{n, c}  = n · c  + c · n  = c`,
  `{n, c†} = n · c† + c† · n = c†`.

These are the duals of the ladder commutators of PR #988 and
follow directly from the orthogonality identities of PRs #982
and #984:

- `{n, c}  = 0  + c  = c`  via `n · c = 0` and `c · n = c`.
- `{n, c†} = c† + 0  = c†` via `n · c† = c†` and `c† · n = 0`.

In each case exactly one of the two products vanishes and the
other equals the ladder operator, so the anticommutator reproduces
the ladder operator itself. Together with the commutator
identities `[n, c] = -c`, `[n, c†] = c†` of PR #988 this expresses
that `n · c = 0`, `c · n = c`, `n · c† = c†`, `c† · n = 0` are the
full per-product breakdown.

The naming convention `_anticommutator_*` mirrors the
`_commutator_*` lemmas of PR #988 (and is also used by the
Gibbs-state `*_anticommutator_im` lemmas in `Quantum/GibbsState/`).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `{n, c} = n · c + c · n = c` (number-annihilation
anticommutator). -/
theorem fermionNumber_anticommutator_fermionAnnihilation :
    fermionNumber * fermionAnnihilation
        + fermionAnnihilation * fermionNumber
      = fermionAnnihilation := by
  rw [fermionNumber_mul_fermionAnnihilation_eq_zero,
    fermionAnnihilation_mul_fermionNumber_eq_fermionAnnihilation,
    zero_add]

/-- `{n, c†} = n · c† + c† · n = c†` (number-creation
anticommutator). -/
theorem fermionNumber_anticommutator_fermionCreation :
    fermionNumber * fermionCreation
        + fermionCreation * fermionNumber
      = fermionCreation := by
  rw [fermionNumber_mul_fermionCreation_eq_fermionCreation,
    fermionCreation_mul_fermionNumber_eq_zero, add_zero]

end LatticeSystem.Fermion

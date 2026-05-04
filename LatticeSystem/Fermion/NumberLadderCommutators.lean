import LatticeSystem.Fermion.AnnihilationNumberIdentities
import LatticeSystem.Fermion.CreationNumberIdentities

/-!
# Fermion ladder commutators `[n, c] = -c` and `[n, c†] = c†`

For the single-mode fermion the number operator `n` and the
ladder operators `c`, `c†` satisfy the standard commutation
relations

  `[n, c]  = n · c  − c · n  = −c`,
  `[n, c†] = n · c† − c† · n =  c†`.

These follow trivially from the orthogonality / projection
identities of PRs #982 and #984:

- `[n, c]  = 0 − c  = −c`  via `n · c = 0` and `c · n = c`.
- `[n, c†] = c† − 0 = c†` via `n · c† = c†` and `c† · n = 0`.

Physically, the adjoint action of `n` (commutation with `n`)
lowers `c` by one unit of fermion number and raises `c†` by one
unit, mirroring the bosonic ladder algebra `[N, a] = -a`,
`[N, a†] = a†`.

The naming convention follows the multi-mode
`fermionMultiNumber_commutator_*` lemmas in
`Fermion/JordanWigner/Number.lean`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `[n, c] = n · c − c · n = −c` (number-annihilation ladder
commutator). -/
theorem fermionNumber_commutator_fermionAnnihilation :
    fermionNumber * fermionAnnihilation
        - fermionAnnihilation * fermionNumber
      = -fermionAnnihilation := by
  rw [fermionNumber_mul_fermionAnnihilation_eq_zero,
    fermionAnnihilation_mul_fermionNumber_eq_fermionAnnihilation,
    zero_sub]

/-- `[n, c†] = n · c† − c† · n = c†` (number-creation ladder
commutator). -/
theorem fermionNumber_commutator_fermionCreation :
    fermionNumber * fermionCreation
        - fermionCreation * fermionNumber
      = fermionCreation := by
  rw [fermionNumber_mul_fermionCreation_eq_fermionCreation,
    fermionCreation_mul_fermionNumber_eq_zero, sub_zero]

end LatticeSystem.Fermion

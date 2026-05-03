import LatticeSystem.Fermion.AnnihilationNumberIdentities
import LatticeSystem.Fermion.CreationNumberIdentities

/-!
# Fermion `c c† c = c` and `c† c c† = c†` (partial-isometry relations)

For the single-mode fermion the operators `c` and `c†` satisfy the
standard partial-isometry identities

  `c · c† · c = c`  and  `c† · c · c† = c†`.

Proofs use the Hermitian projection identities of PRs #982 and #984:

- `c · c† · c = c · n = c` (`fermionAnnihilation_mul_fermionNumber_eq_fermionAnnihilation`).
  But more directly, `c · c† · c = (c · c†) · c = (1 − n) · c = c − n · c = c`,
  which is exactly the proof of PR #982. We use the alternative
  routing `c · c† · c = c · (c† · c) = c · n` and then PR #982.
- `c† · c · c† = c† · (c · c†) = c† · (1 − n) = c† − c† · n = c†`
  via PR #984's `fermionCreation_mul_fermionNumber_eq_zero` and the
  anticommutation.

We instead just invoke the existing identities directly:
- `c · c† · c = c · (c† · c) = c · n = c`.
- `c† · c · c† = (c† · c) · c† = n · c† = c†`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `c · c† · c = c` (partial-isometry left identity). -/
theorem fermionAnnihilation_mul_fermionCreation_mul_fermionAnnihilation :
    fermionAnnihilation * fermionCreation * fermionAnnihilation =
      fermionAnnihilation := by
  rw [mul_assoc,
    show fermionCreation * fermionAnnihilation = fermionNumber from
      (fermionNumber_eq_creation_mul_annihilation).symm,
    fermionAnnihilation_mul_fermionNumber_eq_fermionAnnihilation]

/-- `c† · c · c† = c†` (partial-isometry right identity). -/
theorem fermionCreation_mul_fermionAnnihilation_mul_fermionCreation :
    fermionCreation * fermionAnnihilation * fermionCreation =
      fermionCreation := by
  rw [show fermionCreation * fermionAnnihilation = fermionNumber from
      (fermionNumber_eq_creation_mul_annihilation).symm,
    fermionNumber_mul_fermionCreation_eq_fermionCreation]

end LatticeSystem.Fermion

import LatticeSystem.Fermion.JordanWigner.AnnihilationNumberIdentities
import LatticeSystem.Fermion.JordanWigner.CreationNumberIdentities

/-!
# Multi-mode Jordan–Wigner partial-isometry identities
`c_i · c_i† · c_i = c_i` and `c_i† · c_i · c_i† = c_i†`

Multi-mode (Jordan–Wigner) mirror of single-mode PR #986. The
two same-site partial-isometry identities

  `c_i · c_i† · c_i = c_i`,
  `c_i† · c_i · c_i† = c_i†`.

Direct one-line corollaries of PRs #1001 and #1002 via the
definitional `n_i = c_i† · c_i`:

- `c_i · c_i† · c_i = c_i · (c_i† · c_i) = c_i · n_i = c_i`
  (PR #1001).
- `c_i† · c_i · c_i† = (c_i† · c_i) · c_i† = n_i · c_i† =
   c_i†` (PR #1002).

These are the standard `S · S* · S = S` / `S* · S · S* = S*`
partial-isometry identities of operator algebra, lifted to JW
multi-mode at the same site.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `c_i · c_i† · c_i = c_i` (multi-mode partial-isometry left
identity). -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_mul_fermionMultiAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i * fermionMultiCreation N i *
        fermionMultiAnnihilation N i =
      fermionMultiAnnihilation N i := by
  rw [Matrix.mul_assoc,
    show fermionMultiCreation N i * fermionMultiAnnihilation N i =
      fermionMultiNumber N i from rfl,
    fermionMultiAnnihilation_mul_fermionMultiNumber_eq_fermionMultiAnnihilation]

/-- `c_i† · c_i · c_i† = c_i†` (multi-mode partial-isometry right
identity). -/
theorem fermionMultiCreation_mul_fermionMultiAnnihilation_mul_fermionMultiCreation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiCreation N i * fermionMultiAnnihilation N i *
        fermionMultiCreation N i =
      fermionMultiCreation N i := by
  rw [show fermionMultiCreation N i * fermionMultiAnnihilation N i =
      fermionMultiNumber N i from rfl,
    fermionMultiNumber_mul_fermionMultiCreation_eq_fermionMultiCreation]

end LatticeSystem.Fermion

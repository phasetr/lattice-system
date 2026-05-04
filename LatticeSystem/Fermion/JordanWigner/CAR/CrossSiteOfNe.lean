import LatticeSystem.Fermion.JordanWigner.CAR.CrossSite

/-!
# Symmetric `_of_ne` cross-site CAR identities

The `_lt` versions of the four cross-site CAR identities
(`fermionMultiAnnihilation_anticomm_lt`,
`fermionMultiCreation_anticomm_lt`,
`fermionMultiAnnihilation_creation_anticomm_lt`,
`fermionMultiCreation_annihilation_anticomm_lt`) require
`i.val < j.val`. The four `_of_ne` symmetric forms in this
file accept any `i ≠ j` by trichotomy on `i.val` vs `j.val`:
the `_lt` form covers `i < j` directly, and `j < i` follows by
the symmetry of the anticommutator (swap roles of `i` and `j`,
then `add_comm`).

These complete the symmetric CAR statements needed for upstream
Pauli-analog cross-site lemmas.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `{c_i, c_j} = 0` for any `i ≠ j` (symmetric form of
`fermionMultiAnnihilation_anticomm_lt`). -/
theorem fermionMultiAnnihilation_anticomm_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    fermionMultiAnnihilation N i * fermionMultiAnnihilation N j +
      fermionMultiAnnihilation N j * fermionMultiAnnihilation N i = 0 := by
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact fermionMultiAnnihilation_anticomm_lt N i j hlt
  · exact absurd (Fin.ext heq) hij
  · have h := fermionMultiAnnihilation_anticomm_lt N j i hgt
    exact (add_comm _ _).trans h

/-- `{c_i†, c_j†} = 0` for any `i ≠ j`. -/
theorem fermionMultiCreation_anticomm_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    fermionMultiCreation N i * fermionMultiCreation N j +
      fermionMultiCreation N j * fermionMultiCreation N i = 0 := by
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact fermionMultiCreation_anticomm_lt N i j hlt
  · exact absurd (Fin.ext heq) hij
  · have h := fermionMultiCreation_anticomm_lt N j i hgt
    exact (add_comm _ _).trans h

/-- `{c_i, c_j†} = 0` for any `i ≠ j`. -/
theorem fermionMultiAnnihilation_creation_anticomm_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    fermionMultiAnnihilation N i * fermionMultiCreation N j +
      fermionMultiCreation N j * fermionMultiAnnihilation N i = 0 := by
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact fermionMultiAnnihilation_creation_anticomm_lt N i j hlt
  · exact absurd (Fin.ext heq) hij
  · -- j < i: use `fermionMultiCreation_annihilation_anticomm_lt N j i hgt`
    --        gives c_j† · c_i + c_i · c_j† = 0; rewrite by add_comm.
    have h := fermionMultiCreation_annihilation_anticomm_lt N j i hgt
    exact (add_comm _ _).trans h

/-- `{c_i†, c_j} = 0` for any `i ≠ j`. -/
theorem fermionMultiCreation_annihilation_anticomm_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    fermionMultiCreation N i * fermionMultiAnnihilation N j +
      fermionMultiAnnihilation N j * fermionMultiCreation N i = 0 := by
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact fermionMultiCreation_annihilation_anticomm_lt N i j hlt
  · exact absurd (Fin.ext heq) hij
  · have h := fermionMultiAnnihilation_creation_anticomm_lt N j i hgt
    -- h : c_j · c_i† + c_i† · c_j = 0; need c_i† · c_j + c_j · c_i† = 0.
    exact (add_comm _ _).trans h

end LatticeSystem.Fermion

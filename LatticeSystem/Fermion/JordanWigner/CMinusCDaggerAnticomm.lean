import LatticeSystem.Fermion.JordanWigner.CAR.CrossSiteOfNe

/-!
# Cross-site mixed Pauli-analog anticommutators

Companion to PR #1031: cross-site Pauli-analog anticommutators
for distinct sites:

  `{c_i − c_i†, c_j − c_j†} = 0`,
  `{c_i + c_i†, c_j − c_j†} = 0`,  for `i ≠ j`.

Same expansion technique using PR #1030's `_of_ne` cross-site
CARs:

- `{c_i − c_i†, c_j − c_j†}
    = {c_i, c_j} − {c_i, c_j†} − {c_i†, c_j} + {c_i†, c_j†}
    = 0`.
- `{c_i + c_i†, c_j − c_j†}
    = {c_i, c_j} − {c_i, c_j†} + {c_i†, c_j} − {c_i†, c_j†}
    = 0`.

Together with PR #1031 this shows that all four Pauli-X/iY-
analog operator pairs anticommute across distinct JW sites.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `{c_i − c_i†, c_j − c_j†} = 0` for `i ≠ j` (cross-site
Pauli-iY-analog anticommute). -/
theorem fermionMultiMinus_anticomm_fermionMultiMinus_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    (fermionMultiAnnihilation N i - fermionMultiCreation N i) *
        (fermionMultiAnnihilation N j - fermionMultiCreation N j) +
      (fermionMultiAnnihilation N j - fermionMultiCreation N j) *
        (fermionMultiAnnihilation N i - fermionMultiCreation N i) =
      0 := by
  have h_aa := fermionMultiAnnihilation_anticomm_of_ne hij
  have h_cc := fermionMultiCreation_anticomm_of_ne hij
  have h_ac := fermionMultiAnnihilation_creation_anticomm_of_ne hij
  have h_ca := fermionMultiCreation_annihilation_anticomm_of_ne hij
  -- (c_i - c_i†)(c_j - c_j†) + (c_j - c_j†)(c_i - c_i†)
  --   = ({c_i,c_j} − {c_i,c_j†} − {c_i†,c_j} + {c_i†,c_j†}).
  rw [sub_mul, mul_sub, mul_sub, sub_mul, mul_sub, mul_sub]
  rw [show fermionMultiAnnihilation N i * fermionMultiAnnihilation N j -
        fermionMultiAnnihilation N i * fermionMultiCreation N j -
        (fermionMultiCreation N i * fermionMultiAnnihilation N j -
          fermionMultiCreation N i * fermionMultiCreation N j) +
        (fermionMultiAnnihilation N j * fermionMultiAnnihilation N i -
          fermionMultiAnnihilation N j * fermionMultiCreation N i -
          (fermionMultiCreation N j * fermionMultiAnnihilation N i -
            fermionMultiCreation N j * fermionMultiCreation N i)) =
      (fermionMultiAnnihilation N i * fermionMultiAnnihilation N j +
        fermionMultiAnnihilation N j * fermionMultiAnnihilation N i) -
      (fermionMultiAnnihilation N i * fermionMultiCreation N j +
        fermionMultiCreation N j * fermionMultiAnnihilation N i) -
      (fermionMultiCreation N i * fermionMultiAnnihilation N j +
        fermionMultiAnnihilation N j * fermionMultiCreation N i) +
      (fermionMultiCreation N i * fermionMultiCreation N j +
        fermionMultiCreation N j * fermionMultiCreation N i) from by abel]
  rw [h_aa, h_ac, h_ca, h_cc]
  abel

/-- `{c_i + c_i†, c_j − c_j†} = 0` for `i ≠ j` (cross-site
Pauli-X/iY-analog anticommute). -/
theorem fermionMultiPlus_anticomm_fermionMultiMinus_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    (fermionMultiAnnihilation N i + fermionMultiCreation N i) *
        (fermionMultiAnnihilation N j - fermionMultiCreation N j) +
      (fermionMultiAnnihilation N j - fermionMultiCreation N j) *
        (fermionMultiAnnihilation N i + fermionMultiCreation N i) =
      0 := by
  have h_aa := fermionMultiAnnihilation_anticomm_of_ne hij
  have h_cc := fermionMultiCreation_anticomm_of_ne hij
  have h_ac := fermionMultiAnnihilation_creation_anticomm_of_ne hij
  have h_ca := fermionMultiCreation_annihilation_anticomm_of_ne hij
  rw [add_mul, mul_sub, mul_sub, sub_mul, mul_add, mul_add]
  rw [show fermionMultiAnnihilation N i * fermionMultiAnnihilation N j -
        fermionMultiAnnihilation N i * fermionMultiCreation N j +
        (fermionMultiCreation N i * fermionMultiAnnihilation N j -
          fermionMultiCreation N i * fermionMultiCreation N j) +
        (fermionMultiAnnihilation N j * fermionMultiAnnihilation N i +
          fermionMultiAnnihilation N j * fermionMultiCreation N i -
          (fermionMultiCreation N j * fermionMultiAnnihilation N i +
            fermionMultiCreation N j * fermionMultiCreation N i)) =
      (fermionMultiAnnihilation N i * fermionMultiAnnihilation N j +
        fermionMultiAnnihilation N j * fermionMultiAnnihilation N i) -
      (fermionMultiAnnihilation N i * fermionMultiCreation N j +
        fermionMultiCreation N j * fermionMultiAnnihilation N i) +
      (fermionMultiCreation N i * fermionMultiAnnihilation N j +
        fermionMultiAnnihilation N j * fermionMultiCreation N i) -
      (fermionMultiCreation N i * fermionMultiCreation N j +
        fermionMultiCreation N j * fermionMultiCreation N i) from by abel]
  rw [h_aa, h_ac, h_ca, h_cc]
  abel

end LatticeSystem.Fermion

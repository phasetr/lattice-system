import LatticeSystem.Fermion.JordanWigner.CAR.CrossSiteOfNe

/-!
# Cross-site Pauli-X-analog anticommute `{c_i + c_i†, c_j + c_j†} = 0`

For distinct JW sites, the Pauli-X-analog operators
`(c_i + c_i†)` anticommute:

  `(c_i + c_i†) · (c_j + c_j†) + (c_j + c_j†) · (c_i + c_i†) = 0`
  for `i ≠ j`.

Direct expansion using the four `_of_ne` cross-site CAR
identities (PR #1030):

  `{c_i + c_i†, c_j + c_j†}
   = {c_i, c_j} + {c_i, c_j†} + {c_i†, c_j} + {c_i†, c_j†}
   = 0 + 0 + 0 + 0 = 0`.

This is the JW-string fingerprint: while the on-site spin
operators `σ_x_i` and `σ_x_j` commute, the JW-dressed
combination `c_i + c_i† = jwString_i · σ_x_i` picks up the JW
string sign and anticommutes across sites.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `{c_i + c_i†, c_j + c_j†} = 0` for `i ≠ j` (cross-site
Pauli-X-analog anticommute). -/
theorem fermionMultiPlus_anticomm_fermionMultiPlus_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    (fermionMultiAnnihilation N i + fermionMultiCreation N i) *
        (fermionMultiAnnihilation N j + fermionMultiCreation N j) +
      (fermionMultiAnnihilation N j + fermionMultiCreation N j) *
        (fermionMultiAnnihilation N i + fermionMultiCreation N i) =
      0 := by
  -- Expand both products and use the four cross-site CAR _of_ne lemmas.
  have h_aa := fermionMultiAnnihilation_anticomm_of_ne hij
  have h_cc := fermionMultiCreation_anticomm_of_ne hij
  have h_ac := fermionMultiAnnihilation_creation_anticomm_of_ne hij
  have h_ca := fermionMultiCreation_annihilation_anticomm_of_ne hij
  -- (c_i + c_i†)(c_j + c_j†) + (c_j + c_j†)(c_i + c_i†)
  -- = ({c_i, c_j} + {c_i, c_j†} + {c_i†, c_j} + {c_i†, c_j†})
  -- after expansion.
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add]
  -- Group into four anticomm pairs.
  rw [show fermionMultiAnnihilation N i * fermionMultiAnnihilation N j +
        fermionMultiAnnihilation N i * fermionMultiCreation N j +
        (fermionMultiCreation N i * fermionMultiAnnihilation N j +
          fermionMultiCreation N i * fermionMultiCreation N j) +
        (fermionMultiAnnihilation N j * fermionMultiAnnihilation N i +
          fermionMultiAnnihilation N j * fermionMultiCreation N i +
          (fermionMultiCreation N j * fermionMultiAnnihilation N i +
            fermionMultiCreation N j * fermionMultiCreation N i)) =
      (fermionMultiAnnihilation N i * fermionMultiAnnihilation N j +
        fermionMultiAnnihilation N j * fermionMultiAnnihilation N i) +
      (fermionMultiAnnihilation N i * fermionMultiCreation N j +
        fermionMultiCreation N j * fermionMultiAnnihilation N i) +
      (fermionMultiCreation N i * fermionMultiAnnihilation N j +
        fermionMultiAnnihilation N j * fermionMultiCreation N i) +
      (fermionMultiCreation N i * fermionMultiCreation N j +
        fermionMultiCreation N j * fermionMultiCreation N i) from by abel]
  rw [h_aa, h_ac, h_ca, h_cc]
  abel

end LatticeSystem.Fermion

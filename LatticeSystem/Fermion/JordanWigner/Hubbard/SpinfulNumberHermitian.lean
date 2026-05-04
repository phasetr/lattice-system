import LatticeSystem.Fermion.JordanWigner.Hubbard

/-!
# Spinful Hubbard number-operator Hermiticity

Standalone named Hermiticity lemmas for the spinful number
operators

  `(n_↑(i)).IsHermitian`,
  `(n_↓(i)).IsHermitian`,
  `(n_↑(i) · n_↓(i)).IsHermitian`.

Each is a one-line corollary of the existing
- `fermionMultiNumber_isHermitian`
  (`Fermion/JordanWigner/Operators.lean`), and
- `fermionMultiNumber_mul_isHermitian`
  (`Fermion/JordanWigner/Number.lean`).

These named lemmas make the spinful Hubbard interaction
Hermiticity argument (`hubbardOnSiteInteraction_isHermitian` in
`Fermion/JordanWigner/Hubbard.lean`) re-usable as a per-site
building block.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `(n_↑(i)).IsHermitian`. -/
theorem fermionUpNumber_isHermitian (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i).IsHermitian :=
  fermionMultiNumber_isHermitian (2 * N + 1) (spinfulIndex N i 0)

/-- `(n_↓(i)).IsHermitian`. -/
theorem fermionDownNumber_isHermitian (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownNumber N i).IsHermitian :=
  fermionMultiNumber_isHermitian (2 * N + 1) (spinfulIndex N i 1)

/-- `(n_↑(i) · n_↓(i)).IsHermitian`: the spinful on-site
double-occupancy operator is Hermitian. -/
theorem fermionUpNumber_mul_fermionDownNumber_isHermitian
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i * fermionDownNumber N i).IsHermitian :=
  fermionMultiNumber_mul_isHermitian (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N i 1)

end LatticeSystem.Fermion

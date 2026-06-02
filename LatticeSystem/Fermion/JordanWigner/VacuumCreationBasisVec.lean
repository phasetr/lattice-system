import LatticeSystem.Fermion.JordanWigner.AnnihilationCreationBasisVec
import LatticeSystem.Fermion.JordanWigner.Number

/-!
# Creation operators on the Jordan–Wigner vacuum

This file records the base case of building computational basis states from the
vacuum by creation operators, the starting point for the ordered
creation-operator construction of the Tasaki §11.2 basis states (11.2.3).

The Jordan–Wigner vacuum is the all-empty configuration `basisVec (fun _ => 0)`.
Since no mode below `j` is occupied, the string sign `jwSign N j` of the vacuum
is `1`, so a single creation operator simply produces the single-electron basis
state at `j`:

  `c†_j |vac⟩ = |single electron at j⟩`.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, eq. (11.2.3).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The Jordan–Wigner string sign of the all-empty configuration is `1`:
no mode contributes a `-1`. -/
theorem jwSign_zero_config (N : ℕ) (j : Fin (N + 1)) :
    jwSign N j (fun _ : Fin (N + 1) => (0 : Fin 2)) = 1 := by
  unfold jwSign
  exact Finset.prod_eq_one (fun k _ => rfl)

/-- A single creation operator on the vacuum produces the single-electron
computational basis state at `j`: `c†_j |vac⟩ = |0…0, j ↦ 1⟩`. The string sign
is `1` because the vacuum is empty below `j`. -/
theorem fermionMultiCreation_mulVec_vacuum_eq_basisVec
    (N : ℕ) (j : Fin (N + 1)) :
    (fermionMultiCreation N j).mulVec (fermionMultiVacuum N) =
      basisVec (Function.update (fun _ : Fin (N + 1) => (0 : Fin 2)) j 1) := by
  unfold fermionMultiVacuum
  rw [fermionMultiCreation_mulVec_basisVec, if_pos rfl, jwSign_zero_config,
    one_smul]

end LatticeSystem.Fermion

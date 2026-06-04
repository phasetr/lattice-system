import LatticeSystem.Fermion.JordanWigner.Hubbard.SectorMinEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreSubspace
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Fixed-electron-number hard-core ground subspace (Tasaki §11.5)

Generic machinery for the §11.5 metallic-ferromagnetism results, where the relevant Hilbert
space is the *no-double-occupancy* (hard-core) subspace at a **fixed electron number** `N_e`
(unlike the §11.4 results, which compare total-spin sectors at the flat-band filling without a
hard-core constraint).  For any many-body Hamiltonian `H` on the spinful Jordan–Wigner
backbone we define the candidate states, the ground energy, and the ground subspace at filling
`N_e`.  Both the ferromagnetic t-J model (Proposition 11.24) and the d = 1 decorated Hubbard
model (Theorem 11.26) phrase their ground-state statements on this subspace.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2–§11.5.3 (pp. 442–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The **fixed-electron-number hard-core states**: unit vectors of `EuclideanSpace ℂ` over
the computational configurations that are `N̂`-eigenvectors at the electron number `N_e` and
lie in the no-double-occupancy subspace `H_{N_e}^hc`.  These are the candidate states over
which the ground energy of a hard-core model at filling `N_e` is taken. -/
def fillingHardcoreStates (M Ne : ℕ) :
    Set (EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2)) :=
  {φ | ‖φ‖ = 1 ∧
    (fermionTotalNumber (2 * M + 1)).mulVec φ.ofLp = (Ne : ℂ) • φ.ofLp ∧
    φ.ofLp ∈ hubbardHardcoreSubspace M}

/-- **The ground-state energy of `H` at filling `N_e`**: the infimum of `rayleighOnVec H` over
the unit, `N_e`-electron, hard-core states `fillingHardcoreStates M Ne` — the minimum energy
of the model on its physical Hilbert space `H_{N_e}^hc`. -/
noncomputable def groundEnergyAtFilling {M : ℕ} (H : ManyBodyOp (Fin (2 * M + 2)))
    (Ne : ℕ) : ℝ :=
  ⨅ φ : fillingHardcoreStates M Ne, rayleighOnVec H (φ : EuclideanSpace ℂ _).ofLp

/-- **The ground subspace of `H` at filling `N_e`**: the `H`-eigenspace at the ground energy
`groundEnergyAtFilling H Ne`, intersected with the `N_e`-electron number sector and the
no-double-occupancy subspace `H_{N_e}^hc`.  Its dimension is the ground-state degeneracy. -/
noncomputable def groundSubmoduleAtFilling {M : ℕ} (H : ManyBodyOp (Fin (2 * M + 2)))
    (Ne : ℕ) : Submodule ℂ ((Fin (2 * M + 2) → Fin 2) → ℂ) :=
  Module.End.eigenspace H.mulVecLin (groundEnergyAtFilling H Ne : ℂ) ⊓
    Module.End.eigenspace (fermionTotalNumber (2 * M + 1)).mulVecLin (Ne : ℂ) ⊓
    hubbardHardcoreSubspace M

end LatticeSystem.Fermion

import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeTheorems
import LatticeSystem.Fermion.JordanWigner.Hubbard.GroundSubspaceAtFilling

/-!
# Tasaki §11.1.1: ground-state structure of a ferromagnetic Hubbard model (Proposition 11.2)

When a Hubbard model exhibits saturated ferromagnetism (Definition 11.1, `isSaturatedFerromagnet`),
its ground states simplify drastically: they are exactly the `(2S_max + 1)`-fold `SU(2)` multiplet
built from the lowest-energy all-up Slater state (Tasaki eq. (11.1.4)).  This file records
**Proposition 11.2** as a documented axiom (to be discharged): for the all-to-all Hubbard model
`hubbardHamiltonian N t U` at filling `N + 1` (all `N + 1` sites singly occupied), the ground
eigenspace is a maximal-spin multiplet of total spin `S_max = (N + 1)/2`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Proposition 11.2, eq. (11.1.4), pp. 377–378.
-/

namespace LatticeSystem.Fermion

open Matrix

variable {N : ℕ} (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)

/-- **The ground eigenspace of the Hubbard model at half filling `N + 1`**: the
`hubbardHamiltonian`-eigenspace at the ground energy `groundEnergyAtFilling H (N + 1)`, intersected
with the `(N + 1)`-electron number sector.  Unlike `groundSubmoduleAtFilling`, no hard-core
constraint is imposed, so this captures *every* ground state (relevant for the general — possibly
doubly occupied — Hubbard ground states of Proposition 11.2). -/
noncomputable def hubbardGroundEigenspace :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  Module.End.eigenspace (hubbardHamiltonian N t U).mulVecLin
      (groundEnergyAtFilling (hubbardHamiltonian N t U) (N + 1) : ℂ) ⊓
    Module.End.eigenspace (fermionTotalNumber (2 * N + 1)).mulVecLin (((N + 1 : ℕ) : ℂ))

/-- **Tasaki Proposition 11.2 (ground states of a ferromagnetic Hubbard model), AXIOM.**  If the
all-to-all Hubbard model `hubbardHamiltonian N t U` exhibits saturated ferromagnetism
(`isSaturatedFerromagnet`), then its ground eigenspace at half filling `N + 1` is the
`(N + 2)`-fold maximal-spin multiplet: it has dimension `N + 2 = 2 S_max + 1` and every ground state
is an `(Ŝ_tot)²`-eigenvector at `S_max(S_max + 1)`, `S_max = (N + 1)/2` (Tasaki eq. (11.1.4)).

Tasaki's proof: on the all-up subspace the interaction `Ĥ_int` vanishes, so the model reduces to a
non-interacting one whose lowest state is the all-up Slater determinant; the SU(2) lowering tower of
that state then exhausts the ground eigenspace.  The structural argument is finite-dimensional but
broad (arbitrary hopping `t`); recorded here as a documented axiom (to be discharged), matching the
policy for the other deferred Chapter 11 results. -/
axiom hubbard_proposition_11_2 (hferro : isSaturatedFerromagnet N t U) :
    IsMaximalSpinMultipletSubmodule N (hubbardGroundEigenspace t U) (N + 1)

end LatticeSystem.Fermion

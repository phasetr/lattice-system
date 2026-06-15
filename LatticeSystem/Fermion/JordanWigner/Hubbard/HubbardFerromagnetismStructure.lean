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

/-- **The `E₀`-eigenspace of the Hubbard model at electron filling `Ne`**: the
`hubbardHamiltonian`-eigenspace at energy `E₀`, intersected with the `Ne`-electron number sector.
No hard-core constraint is imposed, so for `E₀` the true ground energy this captures *every* ground
state (relevant for the general — possibly doubly occupied — Hubbard ground states of §11.1). -/
noncomputable def hubbardEigenspaceAt (E₀ : ℂ) (Ne : ℕ) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  Module.End.eigenspace (hubbardHamiltonian N t U).mulVecLin E₀ ⊓
    Module.End.eigenspace (fermionTotalNumber (2 * N + 1)).mulVecLin (Ne : ℂ)

/-- **The `E₀`-eigenspace at half filling `N + 1`**: the special case `Ne = N + 1` of
`hubbardEigenspaceAt`, the natural filling for saturated ferromagnetism (Proposition 11.2). -/
noncomputable def hubbardEigenspaceAtFilling (E₀ : ℂ) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  hubbardEigenspaceAt t U E₀ (N + 1)

/-- **Tasaki Proposition 11.2 (ground states of a ferromagnetic Hubbard model), AXIOM.**  Let `E₀`
be a genuine half-filling ground energy of the all-to-all Hubbard model `hubbardHamiltonian N t U`:
its
`(N + 1)`-electron eigenspace is nonzero (`hne`) and `E₀` is minimal among all energies with a
nonzero `(N + 1)`-electron eigenspace (`hmin`, using the real part as the physical eigenvalue order,
`hubbardHamiltonian` being Hermitian).  If, moreover, the model is ferromagnetic at this ground
energy — every ground state is an `(Ŝ_tot)²`-eigenvector at `S_max(S_max + 1)`, `S_max = (N + 1)/2`
(`hferro`, Definition 11.1 specialised to the ground eigenspace) — then the ground eigenspace is the
`(N + 2)`-fold maximal-spin multiplet (Tasaki eq. (11.1.4)): its dimension is exactly
`N + 2 = 2 S_max + 1`.

The `E₀` of the conclusion is pinned by `hne`/`hmin` to a real ground energy, so the axiom does not
over-claim from a spurious witness; the only content beyond `hferro` (which already supplies the
maximal-spin part of `IsMaximalSpinMultipletSubmodule`) is the dimension count.

Tasaki's proof: on the all-up subspace the interaction `Ĥ_int` vanishes, so the model reduces to a
non-interacting one whose lowest state is the all-up Slater determinant; the SU(2) lowering tower of
that state then exhausts the ground eigenspace.  The structural argument is finite-dimensional but
broad (arbitrary hopping `t`); recorded here as a documented axiom (to be discharged), matching the
policy for the other deferred Chapter 11 results. -/
axiom hubbard_proposition_11_2 (E₀ : ℂ)
    (hne : hubbardEigenspaceAtFilling t U E₀ ≠ ⊥)
    (hmin : ∀ E : ℂ, hubbardEigenspaceAtFilling t U E ≠ ⊥ → E₀.re ≤ E.re)
    (hferro : ∀ v ∈ hubbardEigenspaceAtFilling t U E₀,
      (fermionTotalSpinSquared N).mulVec v
        = (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v) :
    IsMaximalSpinMultipletSubmodule N (hubbardEigenspaceAtFilling t U E₀) (N + 1)

end LatticeSystem.Fermion

import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardFerromagnetismStructure
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Tasaki §11.1.1: impossibility of ferromagnetism for small `U` (Theorem 11.3)

For the all-to-all Hubbard model with a Hermitian hopping matrix `t`, ferromagnetism is impossible
when the on-site repulsion `U` is smaller than the single-particle Fermi gap.  Tasaki's
variational argument (the trial state (11.1.6), a single spin flip in the lowest single-particle
level) shows the all-up Slater state is not the unique ground state once `U < ε_N − ε_1`.

This file builds the **single-particle spectrum** of the hopping matrix (its Hermitian eigenvalues)
and the **Fermi gap** (here, at the project's half-filling convention `N + 1` electrons in `N + 1`
sites, the full bandwidth `max ε − min ε`), and records **Theorem 11.3** as a documented axiom (the
variational discharge, which needs the single-particle eigenbasis fermion operators, is deferred).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.3, eqs. (11.1.5)–(11.1.6), pp. 378–379.
-/

namespace LatticeSystem.Fermion

open Matrix

variable {N : ℕ} (t : Fin (N + 1) → Fin (N + 1) → ℂ)

/-- **The single-particle energies** of the hopping matrix `t`: the (real) Hermitian eigenvalues
`{ε_j}` of `t`.  These are the energies of the one-electron eigenstates that the Slater-determinant
ground states fill. -/
noncomputable def hubbardSingleParticleEnergies (ht : Matrix.IsHermitian t) :
    Fin (N + 1) → ℝ :=
  ht.eigenvalues

/-- **The single-particle Fermi gap** of `t` at the half-filling convention (`N + 1` electrons fully
occupying the `N + 1` one-electron levels): the bandwidth `max_j ε_j − min_j ε_j`.  This is the
quantity `ε_N − ε_1` of Tasaki's Theorem 11.3 specialised to the completely filled up-band — the
energy cost of the lowest single spin flip. -/
noncomputable def hubbardFermiGap (ht : Matrix.IsHermitian t) :
    ℝ :=
  Finset.univ.sup' Finset.univ_nonempty ht.eigenvalues -
    Finset.univ.inf' Finset.univ_nonempty ht.eigenvalues

/-- **Tasaki Theorem 11.3 (impossibility of ferromagnetism for small `U`), AXIOM.**  Let `E₀` be the
genuine half-filling (`N + 1`-electron) ground energy of the Hubbard model with Hermitian hopping
`t`: its eigenspace is nonzero (`hne`) and `E₀` is minimal among energies with a nonzero
`(N + 1)`-electron eigenspace (`hmin`).  If `0 ≤ U` is strictly below the single-particle Fermi gap
`hubbardFermiGap`, then the ground states are **not** all maximal-spin: some ground state has
`S_tot < S_max`, so the
model is not saturated-ferromagnetic.

The conclusion negates the *pinned* ground-state max-spin property (over
`hubbardEigenspaceAtFilling` at the real ground energy `E₀`), not the vacuously-satisfiable
`isSaturatedFerromagnet`, so the
impossibility statement is sound.

Tasaki's proof: the trial state `|Ψ⟩ = ĉ†_{1,↓} ∏_{j=1}^{N-1} ĉ†_{j,↑}|0⟩` (eq. (11.1.6), one spin
flipped into the lowest single-particle level) has energy `E_ferro − (ε_N − ε_1) + U·‖…‖²`, strictly
below `E_ferro` when `U < ε_N − ε_1`, so the maximal-spin all-up state is not the ground state.  The
variational estimate uses the single-particle eigenbasis fermion operators; it is finite-dimensional
but needs that eigenbasis machinery, so it is recorded here as a documented axiom (to be
discharged), matching the policy for the other deferred Chapter 11 results. -/
axiom hubbard_theorem_11_3
    (ht : Matrix.IsHermitian t) (U : ℝ) (E₀ : ℂ)
    (hne : hubbardEigenspaceAtFilling t (U : ℂ) E₀ ≠ ⊥)
    (hmin : ∀ E : ℂ, hubbardEigenspaceAtFilling t (U : ℂ) E ≠ ⊥ → E₀.re ≤ E.re)
    (hU0 : 0 ≤ U) (hUlt : U < hubbardFermiGap t ht) :
    ¬ ∀ v ∈ hubbardEigenspaceAtFilling t (U : ℂ) E₀,
      (fermionTotalSpinSquared N).mulVec v
        = (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v

end LatticeSystem.Fermion

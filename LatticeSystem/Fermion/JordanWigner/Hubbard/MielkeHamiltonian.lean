import LatticeSystem.Fermion.JordanWigner.Hubbard.Graph
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinChargeCommutation

/-!
# Tasaki §11.3.2: the Mielke flat-band Hubbard Hamiltonian

Mielke's flat-band ferromagnetism is the Hubbard model on the *line graph* of a
base lattice, with uniform hopping.  Its Hamiltonian (Tasaki eqs. (11.3.31),
(11.3.6)) is
`Ĥ = t Σ_{{x,y}∈B} ĉ†_{x,σ}ĉ_{y,σ} + 2t Σ_x n̂_x + U Σ_x n̂_{x↑}n̂_{x↓}`,
i.e. the uniform-hopping graph Hubbard Hamiltonian plus a `2t·N̂` shift chosen so
that the ground-state energy is `0` (the second term only shifts the spectrum).

This file defines `mielkeHamiltonian` on an arbitrary `SimpleGraph (Fin (N+1))`
(the line graph enters through the *hypotheses* of Theorems 11.12/11.13, treated
in a companion file) and records its basic symmetries: Hermiticity,
particle-number conservation `[Ĥ, N̂] = 0`, and SU(2) invariance `[Ŝ^±_tot, Ĥ] = 0`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.2, eqs. (11.3.31), (11.3.6).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-- **The Mielke flat-band Hubbard Hamiltonian** on a graph `G` (eqs. (11.3.31),
(11.3.6)): uniform hopping `t` along the edges of `G`, the standard on-site
interaction `U`, and the `2t·N̂` shift placing the ground-state energy at `0`. -/
noncomputable def mielkeHamiltonian (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (t U : ℝ) : ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardHamiltonianOnGraph N G (t : ℂ) (U : ℂ) +
    ((2 * t : ℝ) : ℂ) • fermionTotalNumber (2 * N + 1)

/-- The Mielke Hamiltonian is Hermitian (for real `t, U`). -/
theorem mielkeHamiltonian_isHermitian (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (t U : ℝ) : (mielkeHamiltonian N G t U).IsHermitian := by
  unfold mielkeHamiltonian
  refine (hubbardHamiltonianOnGraph_isHermitian N G ?_ ?_).add ?_
  · simp [Complex.conj_ofReal]
  · simp [Complex.conj_ofReal]
  · exact (fermionTotalNumber_isHermitian (2 * N + 1)).smul
      (isSelfAdjoint_iff.mpr (Complex.conj_ofReal _))

/-- **`[Ĥ_Mielke, N̂] = 0`**: the Mielke Hamiltonian conserves the total particle
number. -/
theorem mielkeHamiltonian_commute_fermionTotalNumber (N : ℕ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (t U : ℝ) :
    Commute (mielkeHamiltonian N G t U) (fermionTotalNumber (2 * N + 1)) := by
  unfold mielkeHamiltonian
  exact (hubbardHamiltonianOnGraph_commute_fermionTotalNumber N G (t : ℂ) (U : ℂ)).add_left
    ((Commute.refl _).smul_left _)

/-- **`[Ŝ^-_tot, Ĥ_Mielke] = 0`**: the Mielke Hamiltonian is SU(2) invariant.  The
uniform graph hopping is a spin-symmetric Hubbard kinetic term, the interaction is
the standard one, and `N̂` commutes with `Ŝ^-_tot`. -/
theorem fermionTotalSpinMinus_commute_mielkeHamiltonian (N : ℕ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (t U : ℝ) :
    Commute (fermionTotalSpinMinus N) (mielkeHamiltonian N G t U) := by
  unfold mielkeHamiltonian
  refine Commute.add_right ?_ ((fermionTotalSpinMinus_commute_fermionTotalNumber N).smul_right _)
  have hJ : ∀ i j, star (couplingOf G (t : ℂ) i j) = couplingOf G (t : ℂ) j i := by
    intro i j
    rw [couplingOf_real G (by simp [Complex.conj_ofReal]), couplingOf_symm]
  exact fermionTotalSpinMinus_commute_hubbardHamiltonian N (couplingOf G (t : ℂ)) (U : ℂ)
    (hJ := hJ) (hU := by simp [Complex.conj_ofReal])

end LatticeSystem.Fermion

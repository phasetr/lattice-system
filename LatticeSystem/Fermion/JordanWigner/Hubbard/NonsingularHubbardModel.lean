import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandEnergyTower
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandNumberConservation
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry

/-!
# Tasaki §11.4: the non-singular Hubbard model (eq. (11.4.23)) and its symmetries

The non-singular Hubbard model perturbs Tasaki's flat-band model (§11.3.1) by a generic
translation-invariant hopping.  Its hopping Hamiltonian is (eq. (11.4.23))
`Ĥ_hop = t Σ_{u,σ} b̂†_{u,σ} b̂_{u,σ} + ζ Σ_{x,y,σ} t_{x,y} ĉ†_{x,σ} ĉ_{x,σ}`,
with `t > 0`, perturbation parameter `ζ ∈ ℝ`, and (with the standard interaction `Ĥ_int`)
the full Hamiltonian `Ĥ = Ĥ_hop + Ĥ_int`.  When `ζ = 0` this is the flat-band model.

Here `nonsingularHubbardHamiltonian` is `flatBandHamiltonian` (the `ζ = 0` model, which
already bundles `t Σ b̂†b̂` and the interaction) plus the `ζ`-perturbation
`ζ • hubbardKinetic` (the generic hopping `Σ t_{x,y} ĉ†ĉ`).  We record its basic
symmetries — Hermiticity, particle-number conservation `[Ĥ, N̂] = 0`, and SU(2) invariance
`[Ŝ^±_tot, Ĥ] = 0` — by combining the corresponding flat-band and kinetic lemmas.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4, eqs. (11.4.23)–(11.4.25).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **The non-singular Hubbard Hamiltonian** (Tasaki eq. (11.4.23)): the flat-band model
(`flatBandHamiltonian`, `= t Σ b̂†b̂ + U Σ n̂↑n̂↓`) perturbed by `ζ` times a generic
translation-invariant hopping `Σ_{x,y,σ} t_{x,y} ĉ†_{x,σ} ĉ_{x,σ}`.  At `ζ = 0` it reduces
to the flat-band model. -/
noncomputable def nonsingularHubbardHamiltonian (K : ℕ) (ν t ζ : ℝ)
    (tPert : Fin (2 * K + 2) → Fin (2 * K + 2) → ℂ) (U : ℝ) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  flatBandHamiltonian K ν t U + (ζ : ℂ) • hubbardKinetic (2 * K + 1) tPert

/-- The non-singular Hubbard Hamiltonian is Hermitian (for real `t, ζ, U` and a Hermitian
perturbation hopping `tPert`). -/
theorem nonsingularHubbardHamiltonian_isHermitian (K : ℕ) (ν t ζ : ℝ)
    {tPert : Fin (2 * K + 2) → Fin (2 * K + 2) → ℂ}
    (hP : ∀ i j, star (tPert i j) = tPert j i) (U : ℝ) :
    (nonsingularHubbardHamiltonian K ν t ζ tPert U).IsHermitian := by
  unfold nonsingularHubbardHamiltonian
  exact (flatBandHamiltonian_isHermitian K ν t U).add
    ((hubbardKinetic_isHermitian (2 * K + 1) hP).smul
      (isSelfAdjoint_iff.mpr (Complex.conj_ofReal ζ)))

/-- **`[Ĥ, N̂] = 0`**: the non-singular Hubbard Hamiltonian conserves the total particle
number. -/
theorem nonsingularHubbardHamiltonian_commute_fermionTotalNumber (K : ℕ) (ν t ζ : ℝ)
    (tPert : Fin (2 * K + 2) → Fin (2 * K + 2) → ℂ) (U : ℝ) :
    Commute (nonsingularHubbardHamiltonian K ν t ζ tPert U)
      (fermionTotalNumber (2 * (2 * K + 1) + 1)) := by
  unfold nonsingularHubbardHamiltonian
  exact (flatBandHamiltonian_commute_fermionTotalNumber K ν t U).add_left
    ((hubbardKinetic_commute_fermionTotalNumber (2 * K + 1) tPert).smul_left _)

/-- **`[Ŝ^+_tot, Ĥ] = 0`**: the non-singular Hubbard Hamiltonian is SU(2) invariant (raising
operator).  The flat-band part and the spin-summed perturbation hopping are both
spin-symmetric. -/
theorem fermionTotalSpinPlus_commute_nonsingularHubbardHamiltonian (K : ℕ) (ν t ζ : ℝ)
    (tPert : Fin (2 * K + 2) → Fin (2 * K + 2) → ℂ) (U : ℝ) :
    Commute (fermionTotalSpinPlus (2 * K + 1))
      (nonsingularHubbardHamiltonian K ν t ζ tPert U) := by
  unfold nonsingularHubbardHamiltonian
  exact (fermionTotalSpinPlus_commute_flatBandHamiltonian K ν t U).add_right
    ((fermionTotalSpinPlus_commute_hubbardKinetic (2 * K + 1) tPert).smul_right _)

/-- **`[Ŝ^-_tot, Ĥ] = 0`**: the non-singular Hubbard Hamiltonian is SU(2) invariant (lowering
operator).  Obtained from the raising-operator version by taking the adjoint, using
`(Ŝ^+_tot)ᴴ = Ŝ^-_tot` and Hermiticity of `Ĥ`. -/
theorem fermionTotalSpinMinus_commute_nonsingularHubbardHamiltonian (K : ℕ) (ν t ζ : ℝ)
    {tPert : Fin (2 * K + 2) → Fin (2 * K + 2) → ℂ}
    (hP : ∀ i j, star (tPert i j) = tPert j i) (U : ℝ) :
    Commute (fermionTotalSpinMinus (2 * K + 1))
      (nonsingularHubbardHamiltonian K ν t ζ tPert U) := by
  have h_plus :=
    (fermionTotalSpinPlus_commute_nonsingularHubbardHamiltonian K ν t ζ tPert U).eq
  have h_H := nonsingularHubbardHamiltonian_isHermitian K ν t ζ hP U
  have h_adj := congrArg Matrix.conjTranspose h_plus
  simp only [Matrix.conjTranspose_mul, fermionTotalSpinPlus_conjTranspose (2 * K + 1),
    h_H.eq] at h_adj
  exact h_adj.symm

end LatticeSystem.Fermion

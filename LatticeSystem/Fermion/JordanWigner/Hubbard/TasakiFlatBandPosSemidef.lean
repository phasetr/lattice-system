import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandEnergyTower
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import Mathlib.Analysis.Matrix.PosDef

/-!
# Tasaki §11.3.1: the flat-band Hamiltonian is PSD and the multiplet are ground states

The final input to the existence half of Theorem 11.11: for `t, U ≥ 0` the
flat-band Hamiltonian is positive-semidefinite,
`Ĥ = t Σ_{u,σ} b̂†_{u,σ} b̂_{u,σ} + U Σ_x n̂_{x↑} n̂_{x↓} ≥ 0`, being a nonnegative
combination of positive-semidefinite terms (each `b̂† b̂ = (b̂)ᴴ b̂`, and each
`n̂_↑ n̂_↓` a Hermitian idempotent projection).  Hence the energy quadratic form
`⟨ψ|Ĥ|ψ⟩` (unnormalized, `rayleighOnVec`) is nonnegative everywhere, while the
zero-energy tower states `(Ŝ^-_tot)^k |Φα,all↑⟩` attain `0`: they lie in the
lowest-energy (kernel) eigenspace — they are **ground states**.

* `flatBandHamiltonian_posSemidef`: `Ĥ.PosSemidef` for `t, U ≥ 0`.
* `flatBand_alphaTower_isGroundState`: each multiplet member minimizes the energy
  quadratic form, `rayleighOnVec Ĥ ((Ŝ^-_tot)^k |Φα⟩) ≤ rayleighOnVec Ĥ ψ` for all
  `ψ`.

Combined with `flatBand_ferromagnetic_multiplet` (linear independence + total spin
`S_max = (K+1)/2`) and the energy tower, this gives the existence half of Tasaki
Theorem 11.11: a `(2 S_max + 1)`-dimensional maximal-spin multiplet of ground
states.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11 (existence half).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped ComplexOrder

/-- Each flat-band kinetic term `b̂†_{u,σ} b̂_{u,σ} = (b̂_{u,σ})ᴴ b̂_{u,σ}` is
positive-semidefinite. -/
theorem flatBandKineticTerm_posSemidef (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) (σ : Fin 2) :
    (flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ).PosSemidef := by
  rw [← flatBandBCreation_eq_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self (flatBandBAnnihilation K ν u σ)

/-- The on-site double-occupancy operator `n̂_{x↑} n̂_{x↓}` is
positive-semidefinite (a Hermitian idempotent, hence `P = Pᴴ P`). -/
theorem hubbardDoubleOccupancy_posSemidef (N : ℕ) (i : Fin (N + 1)) :
    (hubbardDoubleOccupancy N i).PosSemidef := by
  have hEq : (hubbardDoubleOccupancy N i)ᴴ * hubbardDoubleOccupancy N i =
      hubbardDoubleOccupancy N i := by
    rw [(hubbardDoubleOccupancy_isHermitian N i).eq]
    exact fermionUpNumber_mul_fermionDownNumber_sq N i
  have h := Matrix.posSemidef_conjTranspose_mul_self (hubbardDoubleOccupancy N i)
  rwa [hEq] at h

/-- **`Ĥ ≥ 0`**: the flat-band Hamiltonian is positive-semidefinite for
`t, U ≥ 0` — a nonnegative combination of positive-semidefinite kinetic and
interaction terms. -/
theorem flatBandHamiltonian_posSemidef (K : ℕ) (ν t U : ℝ) (ht : 0 ≤ t) (hU : 0 ≤ U) :
    (flatBandHamiltonian K ν t U).PosSemidef := by
  unfold flatBandHamiltonian
  refine Matrix.PosSemidef.add ?_ ?_
  · refine Matrix.PosSemidef.smul ?_ (RCLike.ofReal_nonneg.mpr ht)
    exact Matrix.posSemidef_sum _ (fun u _ =>
      Matrix.posSemidef_sum _ (fun σ _ => flatBandKineticTerm_posSemidef K ν u σ))
  · refine Matrix.PosSemidef.smul ?_ (RCLike.ofReal_nonneg.mpr hU)
    exact Matrix.posSemidef_sum _ (fun x _ => hubbardDoubleOccupancy_posSemidef (2 * K + 1) x)

/-- The energy quadratic form `⟨ψ|Ĥ|ψ⟩` (unnormalized) of the flat-band
Hamiltonian is nonnegative everywhere, for `t, U ≥ 0`. -/
theorem flatBandHamiltonian_rayleighOnVec_nonneg (K : ℕ) (ν t U : ℝ) (ht : 0 ≤ t)
    (hU : 0 ≤ U) (ψ : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :
    0 ≤ rayleighOnVec (flatBandHamiltonian K ν t U) ψ := by
  simpa [rayleighOnVec] using
    (flatBandHamiltonian_posSemidef K ν t U ht hU).re_dotProduct_nonneg ψ

/-- Each ferromagnetic tower state `(Ŝ^-_tot)^k |Φα,all↑⟩` has energy `0`. -/
theorem flatBandHamiltonian_rayleighOnVec_spinMinusPow_alphaAllUpState
    (K : ℕ) (ν t U : ℝ) (k : ℕ) :
    rayleighOnVec (flatBandHamiltonian K ν t U)
      (((fermionTotalSpinMinus (2 * K + 1)) ^ k).mulVec (flatBandAlphaAllUpState K ν)) = 0 := by
  unfold rayleighOnVec
  rw [flatBandHamiltonian_mulVec_spinMinusPow_alphaAllUpState, dotProduct_zero,
    Complex.zero_re]

/-- **The ferromagnetic multiplet are ground states (Theorem 11.11 existence
half).**  For `t, U ≥ 0`, every member `(Ŝ^-_tot)^k |Φα,all↑⟩` of the multiplet
minimizes the energy quadratic form `⟨ψ|Ĥ|ψ⟩`: its value `0` is `≤` that of any
state `ψ` (so, with `Ĥ ⪰ 0`, each lies in the lowest-energy eigenspace — a ground
state).  Together with `flatBand_ferromagnetic_multiplet` (the `K + 2 = 2 S_max + 1` states
are linearly independent and all carry total spin `S_max = (K+1)/2`), this is the
maximal-spin degenerate ground-state multiplet of Tasaki's flat-band ferromagnet. -/
theorem flatBand_alphaTower_isGroundState (K : ℕ) (ν t U : ℝ) (ht : 0 ≤ t) (hU : 0 ≤ U)
    (k : ℕ) (ψ : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :
    rayleighOnVec (flatBandHamiltonian K ν t U)
        (((fermionTotalSpinMinus (2 * K + 1)) ^ k).mulVec (flatBandAlphaAllUpState K ν)) ≤
      rayleighOnVec (flatBandHamiltonian K ν t U) ψ := by
  rw [flatBandHamiltonian_rayleighOnVec_spinMinusPow_alphaAllUpState]
  exact flatBandHamiltonian_rayleighOnVec_nonneg K ν t U ht hU ψ

end LatticeSystem.Fermion

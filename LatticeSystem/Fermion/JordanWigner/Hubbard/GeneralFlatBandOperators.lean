import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinfulVectorOperator
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBand

/-!
# General flat-band mode operators (Tasaki §11.3.4, toward Theorem 11.17)

The fermion operators `â†_{z,σ} = Ĉ†_σ(μ_z)` attached to a *special basis* `{μ_z}_{z∈I}` of the
flat band `h₀ = ker T` (Lemma 11.16, proved as `generalFlatBand_lemma_11_16`).  Tasaki's proof of
Theorem 11.17 (general flat-band ferromagnetism, connectivity form) writes every `D₀`-electron
ground state in terms of these operators (eq. (11.3.46)), reduces it to a spin-system
representation over `I` (eq. (11.3.47)), and propagates the coefficient identity
`C(σ) = C(σ_{z₁↔z₂})` across directly connected basis states (eqs. (11.3.48)–(11.3.49)).  This
module provides the operators and their first properties; it is PR1 of Issue #4363, mirroring the
proved Theorem 11.11 machinery (`TasakiFlatBandBasis.lean` etc.) for an arbitrary special basis.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, Theorem 11.17, pp. 410–412.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {M : ℕ}

/-- **The general flat-band mode creation operator** `â†_{z,σ} = Ĉ†_σ(μ_z)` of the special-basis
state `μ_z` (Tasaki §11.3.4, the operators of eq. (11.3.46)). -/
noncomputable def generalFlatBandCreation (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (z : Fin (M + 1)) (σ : Fin 2) : ManyBodyOp (Fin (2 * M + 2)) :=
  spinfulCreationFromVector M (μ z) σ

/-- **The general flat-band mode annihilation operator** `â_{z,σ} = Ĉ_σ(μ_z)`. -/
noncomputable def generalFlatBandAnnihilation (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (z : Fin (M + 1)) (σ : Fin 2) : ManyBodyOp (Fin (2 * M + 2)) :=
  spinfulAnnihilationFromVector M (μ z) σ

/-- Unfolding lemma: `â†_{z,σ}` is the `μ_z`-weighted sum of the site creation operators. -/
theorem generalFlatBandCreation_eq_sum (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (z : Fin (M + 1)) (σ : Fin 2) :
    generalFlatBandCreation μ z σ
      = ∑ x : Fin (M + 1), μ z x • fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) :=
  rfl

/-- Unfolding lemma: `â_{z,σ}` is the `μ_z`-weighted sum of the site annihilation operators. -/
theorem generalFlatBandAnnihilation_eq_sum (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (z : Fin (M + 1)) (σ : Fin 2) :
    generalFlatBandAnnihilation μ z σ
      = ∑ x : Fin (M + 1), μ z x • fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) :=
  rfl

/-- **The spinful canonical anticommutation relation at general site count**:
`{ĉ_{x,σ}, ĉ†_{y,τ}} = [x = y ∧ σ = τ]` on `M + 1` physical sites.  The general-`M` form of
`spinful_annihilation_creation_anticomm` (which is its `M = 2K+1` delta-chain instance); the
bilinear input for the CAR of the general flat-band mode operators. -/
theorem spinful_annihilation_creation_anticomm_general (M : ℕ) (x y : Fin (M + 1))
    (σ τ : Fin 2) :
    fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) *
        fermionMultiCreation (2 * M + 1) (spinfulIndex M y τ)
      + fermionMultiCreation (2 * M + 1) (spinfulIndex M y τ) *
        fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)
      = if x = y ∧ σ = τ then 1 else 0 := by
  by_cases h : spinfulIndex M x σ = spinfulIndex M y τ
  · obtain ⟨rfl, rfl⟩ := (spinfulIndex_eq_iff M x y σ τ).mp h
    rw [if_pos ⟨rfl, rfl⟩, fermionMultiAnticomm_self]
  · rw [fermionMultiAnnihilation_creation_anticomm_of_ne h,
      if_neg (fun hxy => h ((spinfulIndex_eq_iff M x y σ τ).mpr hxy))]

end LatticeSystem.Fermion

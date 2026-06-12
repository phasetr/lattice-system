import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandMuTransport

/-!
# Spin-configuration representation (Tasaki §11.3.4, eq. 11.3.47, toward Theorem 11.17)

After the transport to the special basis (PR6), a flat-band ground state at filling `D₀` lies in the
`μ`-Slater Fock submodule.  Tasaki's eq. (11.3.47) refines this: using `ĉ_{z,↓}ĉ_{z,↑}|Φ⟩ = 0` for
`z ∈ I` (from `Ĥ_int|Φ⟩ = 0`), there can be no double occupancy of the `â†_{μ_z}` modes, so the ground
state is a superposition over spin configurations `σ : I → {↑,↓}` of
`Π_{z∈I} â†_{μ_z, σ_z}|vac⟩`.

This module begins with the algebraic input: the *site-dual* canonical anticommutation relation
specialised to the index set `I`, where the special basis `{μ_z}` is localised
(`μ_{z'}(z) = δ_{zz'}μ_z(z)`), so the site annihilator `ĉ_{z,σ}` is dual to the mode creator
`â†_{μ_{z'},τ}` with the clean Kronecker structure `δ_{στ}δ_{zz'}μ_z(z)`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.47).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {M : ℕ}

/-- **The site-dual CAR on the index set `I`** (Tasaki §11.3.4): for `z, z' ∈ I`, the special basis's
localisation `μ_{z'}(z) = δ_{zz'}μ_z(z)` collapses the site-dual anticommutator to
`{ĉ_{z,σ}, â†_{μ_{z'},τ}} = δ_{στ}·δ_{zz'}·μ_z(z)·1`. -/
theorem site_annihilation_generalFlatBandCreation_anticomm_localized
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {z z' : Fin (M + 1)} (hz : z ∈ I) (hz' : z' ∈ I) (σ τ : Fin 2) :
    fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ) * generalFlatBandCreation μ z' τ
      + generalFlatBandCreation μ z' τ *
          fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ)
      = (if σ = τ ∧ z = z' then μ z z else 0) • (1 : ManyBodyOp (Fin (2 * M + 2))) := by
  rw [site_annihilation_generalFlatBandCreation_anticomm M μ z z' σ τ]
  obtain ⟨_, _, _, _, hloc⟩ := hbasis
  by_cases hσ : σ = τ
  · by_cases hzz : z = z'
    · subst hzz; rw [if_pos hσ, if_pos ⟨hσ, rfl⟩]
    · rw [if_pos hσ, if_neg (fun h => hzz h.2), hloc z' hz' z hz (fun h => hzz h.symm)]
  · rw [if_neg hσ, if_neg (fun h => hσ h.1)]

end LatticeSystem.Fermion

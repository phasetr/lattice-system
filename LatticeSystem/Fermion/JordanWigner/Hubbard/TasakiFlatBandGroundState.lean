import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandCAR
import LatticeSystem.Fermion.JordanWigner.FockProduct

/-!
# Tasaki §11.3.1: the all-up `α` state and `Ĥ_hop |Φα,all↑⟩ = 0` (eqs. 11.3.8/11.3.9)

The ferromagnetic ground state of Tasaki's flat-band model is built entirely from
the `α` states: `|Φα,all↑⟩ = (∏_p â†_{p,↑}) |vac⟩` (eq. 11.3.9).  Because `b̂_{u,σ}`
anticommutes with every `â†_{p,↑}` (eq. 11.3.7) and annihilates the vacuum, it
annihilates `|Φα,all↑⟩`; hence the (positive-semidefinite) hopping Hamiltonian
`Ĥ_hop = t Σ_{u,σ} b̂†_{u,σ} b̂_{u,σ}` annihilates it too (eq. 11.3.8) — `|Φα,all↑⟩`
is a zero-energy state of `Ĥ_hop`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, eqs. (11.3.8), (11.3.9).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The all-up `α` Slater state `|Φα,all↑⟩ = (∏_p â†_{p,↑}) |vac⟩` (eq. 11.3.9). -/
noncomputable def flatBandAlphaAllUpState (K : ℕ) (ν : ℝ) :
    (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ :=
  ((List.finRange (K + 1)).map (fun p => flatBandACreation K ν p 0)).prod.mulVec
    (fermionMultiVacuum (2 * (2 * K + 1) + 1))

/-- `b̂_{u,σ}` annihilates the vacuum (it is a combination of annihilation
operators). -/
theorem flatBandBAnnihilation_mulVec_vacuum (K : ℕ) (ν : ℝ) (u : Fin (K + 1))
    (σ : Fin 2) :
    (flatBandBAnnihilation K ν u σ).mulVec
      (fermionMultiVacuum (2 * (2 * K + 1) + 1)) = 0 := by
  unfold flatBandBAnnihilation
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [Matrix.smul_mulVec, fermionMultiAnnihilation_mulVec_vacuum, smul_zero]

/-- **`b̂_{u,σ} |Φα,all↑⟩ = 0`** (the zero-energy condition (11.3.11) at the
all-up state): `b̂` anticommutes through the `â†` product to the vacuum. -/
theorem flatBandBAnnihilation_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) (u : Fin (K + 1))
    (σ : Fin 2) :
    (flatBandBAnnihilation K ν u σ).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
  unfold flatBandAlphaAllUpState
  rw [Matrix.mulVec_mulVec]
  exact anticomm_listProd_mulVec_vacuum (flatBandBAnnihilation K ν u σ)
    (fun p => flatBandACreation K ν p 0) (List.finRange (K + 1))
    (flatBandBAnnihilation_mulVec_vacuum K ν u σ)
    (fun p _ => flatBandBAnnihilation_ACreation_anticomm K ν u p σ 0)

/-- The flat-band hopping Hamiltonian `Ĥ_hop = t Σ_{u,σ} b̂†_{u,σ} b̂_{u,σ}`
(eq. 11.3.5), separated from the full Hamiltonian. -/
noncomputable def flatBandHopping (K : ℕ) (ν t : ℝ) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  (t : ℂ) • ∑ u : Fin (K + 1), ∑ σ : Fin 2,
    flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ

/-- **Tasaki eq. (11.3.8): `Ĥ_hop |Φα,all↑⟩ = 0`.**  Each kinetic term
`b̂†_{u,σ} b̂_{u,σ}` annihilates `|Φα,all↑⟩` because `b̂_{u,σ}` does. -/
theorem flatBandHopping_mulVec_alphaAllUpState (K : ℕ) (ν t : ℝ) :
    (flatBandHopping K ν t).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
  unfold flatBandHopping
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
  rw [Finset.sum_eq_zero (fun u _ => ?_), smul_zero]
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  rw [← Matrix.mulVec_mulVec, flatBandBAnnihilation_mulVec_alphaAllUpState,
    Matrix.mulVec_zero]

end LatticeSystem.Fermion

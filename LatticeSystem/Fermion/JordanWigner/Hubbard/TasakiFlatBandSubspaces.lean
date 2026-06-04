import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandNumberConservation

/-!
# Tasaki §11.3.1: the `α`-Fock and `b̂`-kernel subspaces (uniqueness framework)

Submodule scaffolding for the uniqueness half of Theorem 11.11.

* `flatBandAlphaFockSubmodule`: the span of all `α`-band Slater states
  `(∏_q â†_{q}) |vac⟩` — the subspace built entirely from the flat band.  The
  ferromagnetic ground state `|Φα,all↑⟩` lives in it
  (`flatBandAlphaAllUpState_mem_alphaFockSubmodule`).
* `flatBandBKernelSubmodule`: the common kernel `⨅_{u,σ} ker b̂_{u,σ}`.  Every
  ground state lies in it (`flatBand_groundState_mem_BKernelSubmodule`), by the
  frustration-free condition (11.3.11).

Tasaki's uniqueness argument is exactly the inclusion
`flatBandBKernelSubmodule ⊆ flatBandAlphaFockSubmodule` (no `β`-occupation forces
the state into the flat band) followed by the symmetric/maximal-spin
classification.  This file sets up the two subspaces and the easy memberships.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- An `α`-band Slater state `(∏_{q ∈ qs} â†_{q.1, q.2}) |vac⟩`, indexed by an
ordered list of `(orbital, spin)` modes. -/
noncomputable def flatBandAlphaSlaterState (K : ℕ) (ν : ℝ)
    (qs : List (Fin (K + 1) × Fin 2)) : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ :=
  ((qs.map (fun q => flatBandACreation K ν q.1 q.2)).prod).mulVec
    (fermionMultiVacuum (2 * (2 * K + 1) + 1))

/-- The `α`-Fock subspace: the span of all `α`-band Slater states. -/
noncomputable def flatBandAlphaFockSubmodule (K : ℕ) (ν : ℝ) :
    Submodule ℂ ((Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :=
  Submodule.span ℂ (Set.range (flatBandAlphaSlaterState K ν))

/-- The all-up ferromagnetic state `|Φα,all↑⟩` is the `α`-Slater state of the
fully filled up-band, hence lies in the `α`-Fock subspace. -/
theorem flatBandAlphaAllUpState_mem_alphaFockSubmodule (K : ℕ) (ν : ℝ) :
    flatBandAlphaAllUpState K ν ∈ flatBandAlphaFockSubmodule K ν := by
  apply Submodule.subset_span
  refine ⟨(List.finRange (K + 1)).map (fun p => (p, (0 : Fin 2))), ?_⟩
  unfold flatBandAlphaSlaterState flatBandAlphaAllUpState
  rw [List.map_map]
  rfl

/-- The common kernel `⨅_{u,σ} ker b̂_{u,σ}` of all flat-band `b̂` annihilations. -/
noncomputable def flatBandBKernelSubmodule (K : ℕ) (ν : ℝ) :
    Submodule ℂ ((Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :=
  ⨅ u : Fin (K + 1), ⨅ σ : Fin 2,
    LinearMap.ker (flatBandBAnnihilation K ν u σ).mulVecLin

/-- A vector lies in the `b̂`-kernel subspace iff every `b̂_{u,σ}` annihilates it. -/
theorem mem_flatBandBKernelSubmodule_iff (K : ℕ) (ν : ℝ)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ} :
    v ∈ flatBandBKernelSubmodule K ν ↔
      ∀ (u : Fin (K + 1)) (σ : Fin 2), (flatBandBAnnihilation K ν u σ).mulVec v = 0 := by
  simp only [flatBandBKernelSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    Matrix.mulVecLin_apply]

/-- **Every ground state lies in the `b̂`-kernel subspace** (frustration-free
condition (11.3.11)): all `b̂_{u,σ}` annihilate it. -/
theorem flatBand_groundState_mem_BKernelSubmodule (K : ℕ) (ν t U : ℝ) (ht : 0 < t)
    (hU : 0 ≤ U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0) :
    v ∈ flatBandBKernelSubmodule K ν :=
  (mem_flatBandBKernelSubmodule_iff K ν).mpr
    (fun u σ => flatBand_groundState_BAnnihilation_mulVec_eq_zero K ν t U ht hU hv u σ)

end LatticeSystem.Fermion

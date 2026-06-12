import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandOperators

/-!
# General flat-band mode monomials (Tasaki §11.3.4, toward eq. (11.3.46))

Towards the hard direction of Tasaki's Fock-spanning equation (11.3.46): a `D₀`-electron flat-band
ground state is a linear combination of `â†`-monomials over the flat band.  The Theorem 11.11
occupation-basis spanning machinery (`TasakiFlatBandModeMonomial.lean`, `ModeReorder.lean`,
`OccBasis.lean`) is **generic in the single-particle basis**, so we re-develop it here over an
arbitrary basis of the single-particle space, with mode creation
`Ĉ†_σ(e i) = spinfulCreationFromVector M (e i) σ`.

This module records the first ingredient: the creation–creation anticommutation
`{Ĉ†_σ(φ), Ĉ†_τ(ψ)} = 0` (the algebraic input for reordering a Fock monomial into canonical
order) and the nilpotency `(Ĉ†_σ(φ))² = 0`.  Mirrors
`flatBandMode_creation_creation_anticomm`/`flatBandModeCreation_sq` of the Theorem 11.11 chain.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.46).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {M : ℕ}

/-- The spinful creation–creation anticommutation `{ĉ†_{x,σ}, ĉ†_{y,τ}} = 0` at general site
count `M + 1` (the general-`M` form of `spinful_creation_creation_anticomm`). -/
theorem spinful_creation_creation_anticomm_general (M : ℕ) (x y : Fin (M + 1)) (σ τ : Fin 2) :
    fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
        fermionMultiCreation (2 * M + 1) (spinfulIndex M y τ)
      + fermionMultiCreation (2 * M + 1) (spinfulIndex M y τ) *
        fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) = 0 := by
  by_cases h : spinfulIndex M x σ = spinfulIndex M y τ
  · rw [h, fermionMultiCreation_sq, add_zero]
  · exact fermionMultiCreation_anticomm_of_ne h

/-- **Bilinear creation–creation anticommutation** `{Ĉ†_σ(φ), Ĉ†_τ(ψ)} = 0`.  The bilinear double
sum of the spinful site anticommutations (all zero) vanishes termwise.  Specialises to
`{â†_{z,σ}, â†_{z',τ}} = 0` for the general flat-band mode operators. -/
theorem spinfulFromVector_creation_creation_anticomm (M : ℕ) (φ ψ : Fin (M + 1) → ℂ)
    (σ τ : Fin 2) :
    spinfulCreationFromVector M φ σ * spinfulCreationFromVector M ψ τ
      + spinfulCreationFromVector M ψ τ * spinfulCreationFromVector M φ σ = 0 := by
  have hkey : spinfulCreationFromVector M φ σ * spinfulCreationFromVector M ψ τ
      + spinfulCreationFromVector M ψ τ * spinfulCreationFromVector M φ σ
      = ∑ x : Fin (M + 1), ∑ y : Fin (M + 1), (φ x * ψ y) •
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
              fermionMultiCreation (2 * M + 1) (spinfulIndex M y τ)
            + fermionMultiCreation (2 * M + 1) (spinfulIndex M y τ) *
              fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ)) := by
    simp only [spinfulCreationFromVector]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm _ (ψ y), smul_mul_assoc,
      mul_smul_comm, smul_smul, mul_comm (ψ y), ← smul_add]
  rw [hkey]
  refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => ?_))
  rw [spinful_creation_creation_anticomm_general, smul_zero]

/-- The square of a smeared creation operator vanishes: `(Ĉ†_σ(φ))² = 0` (from the diagonal of the
creation–creation anticommutation, `2·(Ĉ†)² = 0`). -/
theorem spinfulCreationFromVector_sq (M : ℕ) (φ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    spinfulCreationFromVector M φ σ * spinfulCreationFromVector M φ σ = 0 := by
  have h2 := spinfulFromVector_creation_creation_anticomm M φ φ σ σ
  rw [← two_smul ℂ] at h2
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- A **general-basis Fock monomial**: the ordered product of mode-creations `Ĉ†_σ(e i)` (for
`(i, σ)` ranging over the list `qs`) applied to the vacuum, for a single-particle basis `e` of the
`M + 1` modes.  Mirrors `flatBandModeMonomial` for an arbitrary basis (instantiated at the spectral
eigenbasis of `T` for eq. (11.3.46)). -/
noncomputable def generalModeMonomial (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (qs : List (Fin (M + 1) × Fin 2)) : (Fin (2 * M + 2) → Fin 2) → ℂ :=
  ((qs.map (fun q => spinfulCreationFromVector M (e q.1) q.2)).prod).mulVec
    (fermionMultiVacuum (2 * M + 1))

/-- The span of all general-basis Fock monomials (the candidate full Fock basis span). -/
noncomputable def generalModeFockSubmodule
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) :
    Submodule ℂ ((Fin (2 * M + 2) → Fin 2) → ℂ) :=
  Submodule.span ℂ (Set.range (generalModeMonomial e))

/-- Every general-basis Fock monomial lies in the span. -/
theorem generalModeMonomial_mem (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (qs : List (Fin (M + 1) × Fin 2)) :
    generalModeMonomial e qs ∈ generalModeFockSubmodule e :=
  Submodule.subset_span ⟨qs, rfl⟩

/-- Prepending a mode-creation `Ĉ†_σ(e i)` to a monomial conses `(i, σ)` onto its list. -/
theorem spinfulCreation_mulVec_generalModeMonomial
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (i : Fin (M + 1)) (σ : Fin 2)
    (qs : List (Fin (M + 1) × Fin 2)) :
    (spinfulCreationFromVector M (e i) σ).mulVec (generalModeMonomial e qs)
      = generalModeMonomial e ((i, σ) :: qs) := by
  unfold generalModeMonomial
  rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]

end LatticeSystem.Fermion

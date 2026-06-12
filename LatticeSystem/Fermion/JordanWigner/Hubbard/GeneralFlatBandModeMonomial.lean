import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandOperators
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiBasis
import LatticeSystem.Math.ListProdMulVec

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

/-- The site creation operator is the singleton smeared creator: `Ĉ†_σ(e_x) = ĉ†_{x,σ}`. -/
theorem spinfulCreationFromVector_single (M : ℕ) (x : Fin (M + 1)) (σ : Fin 2) :
    spinfulCreationFromVector M (Pi.single x 1) σ
      = fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) := by
  rw [spinfulCreationFromVector, Finset.sum_eq_single x]
  · rw [Pi.single_eq_same, one_smul]
  · intro y _ hyx
    rw [Pi.single_eq_of_ne hyx, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- `Ĉ†_σ` carries finite sums of single-particle states to sums of creators. -/
theorem spinfulCreationFromVector_sum {ι : Type*} (M : ℕ) (s : Finset ι)
    (f : ι → Fin (M + 1) → ℂ) (σ : Fin 2) :
    spinfulCreationFromVector M (∑ i ∈ s, f i) σ
      = ∑ i ∈ s, spinfulCreationFromVector M (f i) σ := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, spinfulCreationFromVector_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, spinfulCreationFromVector_add, ih]

/-- The span is invariant under each mode-creation `Ĉ†_σ(e i)`. -/
theorem spinfulCreation_basis_mulVec_mem
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (i : Fin (M + 1)) (σ : Fin 2)
    {w : (Fin (2 * M + 2) → Fin 2) → ℂ} (hw : w ∈ generalModeFockSubmodule e) :
    (spinfulCreationFromVector M (e i) σ).mulVec w ∈ generalModeFockSubmodule e := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨qs, rfl⟩
    rw [spinfulCreation_mulVec_generalModeMonomial]
    exact generalModeMonomial_mem _ _
  · rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

/-- The span is invariant under every site creation `ĉ†_{x,σ}`, because a site creation is the
`e`-expansion `∑_i (e.repr e_x) i • Ĉ†_σ(e i)` of the mode-creations. -/
theorem fermionMultiCreation_spinful_mulVec_generalModeFock_mem
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (x : Fin (M + 1)) (σ : Fin 2)
    {w : (Fin (2 * M + 2) → Fin 2) → ℂ} (hw : w ∈ generalModeFockSubmodule e) :
    (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ)).mulVec w
      ∈ generalModeFockSubmodule e := by
  rw [← spinfulCreationFromVector_single M x σ]
  have hrepr : spinfulCreationFromVector M (Pi.single x 1) σ
      = ∑ i, e.repr (Pi.single x (1 : ℂ)) i • spinfulCreationFromVector M (e i) σ := by
    conv_lhs => rw [← e.sum_repr (Pi.single x (1 : ℂ))]
    rw [spinfulCreationFromVector_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [spinfulCreationFromVector_smul]
  rw [hrepr, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ (spinfulCreation_basis_mulVec_mem e i σ hw)

/-- The vacuum lies in the general-basis monomial span (the empty monomial). -/
theorem fermionMultiVacuum_mem_generalModeFock
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) :
    fermionMultiVacuum (2 * M + 1) ∈ generalModeFockSubmodule e := by
  have h := generalModeMonomial_mem e []
  simpa [generalModeMonomial] using h

/-- The span is invariant under every site creation `ĉ†_j` (any spinful mode `j`). -/
theorem fermionMultiCreation_mulVec_generalModeFock_mem
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (j : Fin (2 * M + 2))
    {w : (Fin (2 * M + 2) → Fin 2) → ℂ} (hw : w ∈ generalModeFockSubmodule e) :
    (fermionMultiCreation (2 * M + 1) j).mulVec w ∈ generalModeFockSubmodule e := by
  obtain ⟨x, σ, rfl⟩ := exists_spinfulIndex M j
  exact fermionMultiCreation_spinful_mulVec_generalModeFock_mem e x σ hw

/-- Any ordered product of site creations on the vacuum lies in the monomial span. -/
theorem listProd_creation_mulVec_vacuum_generalModeFock_mem
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (js : List (Fin (2 * M + 2))) :
    ((js.map (fermionMultiCreation (2 * M + 1))).prod).mulVec (fermionMultiVacuum (2 * M + 1))
      ∈ generalModeFockSubmodule e :=
  LatticeSystem.Math.listProd_mulVec_mem
    (fun _ hMmem _ hwmem => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hMmem
      exact fermionMultiCreation_mulVec_generalModeFock_mem e j hwmem)
    (fermionMultiVacuum_mem_generalModeFock e)

/-- **The general-basis Fock monomials span the whole space** (`= ⊤`).  Every computational basis
vector `basisVec c` is the ordered product of site creations over the sorted occupied modes of `c`
on the vacuum, hence lies in the span. -/
theorem generalModeFockSubmodule_eq_top
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) :
    generalModeFockSubmodule e = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  have hbasis : ∀ c : Fin (2 * M + 2) → Fin 2, basisVec c ∈ generalModeFockSubmodule e := by
    intro c
    have hsorted : ((Finset.univ.filter (fun x => c x = 1)).sort (· ≤ ·)).Pairwise (· < ·) :=
      List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort _)
    have hocc : occupationOf ((Finset.univ.filter (fun x => c x = 1)).sort (· ≤ ·)) = c := by
      funext k
      simp only [occupationOf, Finset.mem_sort, Finset.mem_filter, Finset.mem_univ, true_and]
      generalize c k = m
      fin_cases m <;> simp
    rw [← hocc, ← prod_creation_mulVec_vacuum (2 * M + 1) _ hsorted]
    exact listProd_creation_mulVec_vacuum_generalModeFock_mem e _
  have hv : v = ∑ c, v c • basisVec c := by
    funext τ
    simp only [Finset.sum_apply, Pi.smul_apply, basisVec_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hv]
  exact Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (hbasis c))

end LatticeSystem.Fermion

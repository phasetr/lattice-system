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

/-- Expansion of the product `Ĉ_σ(φ)·Ĉ†_τ(ψ)` into the double sum of sitewise products. -/
private theorem fromVector_mul_expand (M : ℕ) (φ ψ : Fin (M + 1) → ℂ) (σ τ : Fin 2) :
    spinfulAnnihilationFromVector M φ σ * spinfulCreationFromVector M ψ τ
      = ∑ x : Fin (M + 1), ∑ y : Fin (M + 1), (φ x * ψ y) •
          (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) *
            fermionMultiCreation (2 * M + 1) (spinfulIndex M y τ)) := by
  simp only [spinfulAnnihilationFromVector, spinfulCreationFromVector, Finset.sum_mul,
    Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [mul_comm (ψ y) (φ x)]

/-- Expansion of the reversed product `Ĉ†_τ(ψ)·Ĉ_σ(φ)` into the double sum of sitewise
products (annihilation index outer, matching `fromVector_mul_expand`). -/
private theorem fromVector_mul_expand' (M : ℕ) (φ ψ : Fin (M + 1) → ℂ) (σ τ : Fin 2) :
    spinfulCreationFromVector M ψ τ * spinfulAnnihilationFromVector M φ σ
      = ∑ x : Fin (M + 1), ∑ y : Fin (M + 1), (φ x * ψ y) •
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M y τ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)) := by
  simp only [spinfulAnnihilationFromVector, spinfulCreationFromVector, Finset.sum_mul,
    Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- **Bilinear CAR for single-particle-state operators** (Tasaki §11.3.4 input):
`{Ĉ_σ(φ), Ĉ†_τ(ψ)} = δ_{στ}·(Σ_x φ(x)ψ(x))·1`.  Expand both products into double sums
(`fromVector_mul_expand`, `fromVector_mul_expand'`), apply the sitewise CAR
`spinful_annihilation_creation_anticomm_general` termwise, and collapse the Kronecker delta. -/
theorem spinfulFromVector_annihilation_creation_anticomm (M : ℕ)
    (φ ψ : Fin (M + 1) → ℂ) (σ τ : Fin 2) :
    spinfulAnnihilationFromVector M φ σ * spinfulCreationFromVector M ψ τ
      + spinfulCreationFromVector M ψ τ * spinfulAnnihilationFromVector M φ σ
      = (if σ = τ then (∑ x : Fin (M + 1), φ x * ψ x) else 0)
          • (1 : ManyBodyOp (Fin (2 * M + 2))) := by
  rw [fromVector_mul_expand, fromVector_mul_expand', ← Finset.sum_add_distrib]
  by_cases hστ : σ = τ
  · subst hστ
    rw [if_pos rfl]
    have hy : ∀ x y : Fin (M + 1),
        ((φ x * ψ y) • (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) *
            fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ))
          + (φ x * ψ y) • (fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)))
        = if x = y then (φ x * ψ y) • (1 : ManyBodyOp (Fin (2 * M + 2))) else 0 := by
      intro x y
      rw [← smul_add, spinful_annihilation_creation_anticomm_general]
      by_cases hxy : x = y
      · rw [if_pos ⟨hxy, rfl⟩, if_pos hxy]
      · rw [if_neg (fun h => hxy h.1), if_neg hxy, smul_zero]
    have hx : ∀ x : Fin (M + 1),
        (∑ y : Fin (M + 1),
          ((φ x * ψ y) • (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) *
              fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ))
            + (φ x * ψ y) • (fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ))))
        = (φ x * ψ x) • (1 : ManyBodyOp (Fin (2 * M + 2))) := by
      intro x
      simp only [hy]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ x)]
    calc (∑ x : Fin (M + 1), ((∑ y : Fin (M + 1), (φ x * ψ y) •
            (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) *
              fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ)))
          + ∑ y : Fin (M + 1), (φ x * ψ y) •
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ))))
        = ∑ x : Fin (M + 1), (φ x * ψ x) • (1 : ManyBodyOp (Fin (2 * M + 2))) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_add_distrib]
          exact hx x
      _ = (∑ x : Fin (M + 1), φ x * ψ x) • (1 : ManyBodyOp (Fin (2 * M + 2))) := by
          rw [Finset.sum_smul]
  · rw [if_neg hστ, zero_smul]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [← smul_add, spinful_annihilation_creation_anticomm_general,
      if_neg (fun h => hστ h.2), smul_zero]

/-- The single-particle operator of a coordinate delta vector is the plain site operator:
`Ĉ_σ(e_z) = ĉ_{z,σ}`. -/
theorem spinfulAnnihilationFromVector_single (M : ℕ) (z : Fin (M + 1)) (σ : Fin 2) :
    spinfulAnnihilationFromVector M (Pi.single z 1) σ
      = fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ) := by
  rw [spinfulAnnihilationFromVector, Finset.sum_eq_single z]
  · rw [Pi.single_eq_same, one_smul]
  · intro y _ hyz
    rw [Pi.single_eq_of_ne hyz, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ z) h

/-- **Site-dual CAR for the flat-band mode creators** (the peel input for eq. (11.3.46)):
`{ĉ_{z,σ}, â†_{z',τ}} = δ_{στ}·μ_{z'}(z)·1`.  The site annihilation operator at `z` reads off
the `z`-coordinate of the mode vector; on the index set `I` of a special basis the
biorthogonality `μ_{z'}(z) = δ_{zz'}·μ_z(z)` then makes this the dual pairing. -/
theorem site_annihilation_generalFlatBandCreation_anticomm (M : ℕ)
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (z z' : Fin (M + 1)) (σ τ : Fin 2) :
    fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ) * generalFlatBandCreation μ z' τ
      + generalFlatBandCreation μ z' τ *
          fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ)
      = (if σ = τ then μ z' z else 0) • (1 : ManyBodyOp (Fin (2 * M + 2))) := by
  rw [← spinfulAnnihilationFromVector_single M z σ, generalFlatBandCreation,
    spinfulFromVector_annihilation_creation_anticomm]
  have hcoef : (∑ x : Fin (M + 1), (Pi.single z 1 : Fin (M + 1) → ℂ) x * μ z' x)
      = μ z' z := by
    rw [Finset.sum_eq_single z]
    · rw [Pi.single_eq_same, one_mul]
    · intro y _ hyz
      rw [Pi.single_eq_of_ne hyz, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ z) h
  rw [hcoef]

/-- A **general flat-band Slater state** `(∏_{q ∈ qs} â†_{q.1, q.2}) |vac⟩`, indexed by an
ordered list of `(index-site, spin)` modes of a special basis (the states of eq. (11.3.46)). -/
noncomputable def generalFlatBandSlaterState (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (qs : List (Fin (M + 1) × Fin 2)) : (Fin (2 * M + 2) → Fin 2) → ℂ :=
  ((qs.map (fun q => generalFlatBandCreation μ q.1 q.2)).prod).mulVec
    (fermionMultiVacuum (2 * M + 1))

/-- The **general flat-band Fock subspace**: the span of all `â†`-Slater states of a special
basis — the right-hand side of Tasaki's eq. (11.3.46). -/
noncomputable def generalFlatBandFockSubmodule (μ : Fin (M + 1) → Fin (M + 1) → ℂ) :
    Submodule ℂ ((Fin (2 * M + 2) → Fin 2) → ℂ) :=
  Submodule.span ℂ (Set.range (generalFlatBandSlaterState μ))

/-- **The site annihilator kills a Slater state whose mode vectors vanish at its site** (the
peel of eq. (11.3.46)): if `μ_{q}(z) = 0` for every mode `q` in the list, then
`ĉ_{z,σ}` anticommutes through every `â†` factor (site-dual CAR with vanishing pairing) and
annihilates the vacuum.  On the index set `I` this is exactly the biorthogonality statement for
`z ∈ I` not among the listed modes. -/
theorem site_annihilation_mulVec_generalFlatBandSlaterState (M : ℕ)
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (z : Fin (M + 1)) (σ : Fin 2)
    (qs : List (Fin (M + 1) × Fin 2)) (hz : ∀ q ∈ qs, μ q.1 z = 0) :
    (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ)).mulVec
      (generalFlatBandSlaterState μ qs) = 0 := by
  revert hz
  unfold generalFlatBandSlaterState
  induction qs with
  | nil =>
    intro _
    simpa using fermionMultiAnnihilation_mulVec_vacuum (2 * M + 1) (spinfulIndex M z σ)
  | cons q qs ih =>
    intro hz
    have hanti := site_annihilation_generalFlatBandCreation_anticomm M μ z q.1 σ q.2
    rw [hz q List.mem_cons_self] at hanti
    have hanti0 : fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ) *
        generalFlatBandCreation μ q.1 q.2
        + generalFlatBandCreation μ q.1 q.2 *
          fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ) = 0 := by
      rw [hanti]
      by_cases h : σ = q.2 <;> simp [h]
    rw [List.map_cons, List.prod_cons, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      eq_neg_of_add_eq_zero_left hanti0, Matrix.neg_mul, Matrix.mul_assoc,
      Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ih (fun q' hq' => hz q' (List.mem_cons_of_mem q hq')), Matrix.mulVec_zero, neg_zero]

/-- Every `â†`-Slater state lies in the general flat-band Fock subspace (span membership). -/
theorem generalFlatBandSlaterState_mem_fockSubmodule
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (qs : List (Fin (M + 1) × Fin 2)) :
    generalFlatBandSlaterState μ qs ∈ generalFlatBandFockSubmodule μ :=
  Submodule.subset_span ⟨qs, rfl⟩

/-- **The single peeled contribution** of position `i` when the site annihilator `ĉ_{x,σ}`
passes through a general flat-band Slater list: amplitude `μ_{qs[i].1}(x)` on a spin match and
Koszul sign `(-1)^i`, leaving the Slater state with the `i`-th mode removed (the general-basis
analogue of `flatBandModePeelTerm`, toward the eq. (11.3.48) expansion). -/
noncomputable def generalFlatBandPeelTerm (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (x : Fin (M + 1)) (σ : Fin 2) (qs : List (Fin (M + 1) × Fin 2)) (i : Fin qs.length) :
    (Fin (2 * M + 2) → Fin 2) → ℂ :=
  ((-1 : ℂ) ^ (i : ℕ)) •
    ((if (qs.get i).2 = σ then μ (qs.get i).1 x else 0) •
      generalFlatBandSlaterState μ (qs.eraseIdx i))

/-- Acting with one more mode creator prepends it to the Slater list:
`â†_{z,σ} |qs⟩ = |(z,σ) :: qs⟩`. -/
theorem generalFlatBandCreation_mulVec_slaterState (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (z : Fin (M + 1)) (σ : Fin 2) (qs : List (Fin (M + 1) × Fin 2)) :
    (generalFlatBandCreation μ z σ).mulVec (generalFlatBandSlaterState μ qs)
      = generalFlatBandSlaterState μ ((z, σ) :: qs) := by
  unfold generalFlatBandSlaterState
  rw [List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]

/-- **The site-annihilation peel** (the engine of Tasaki's eq. (11.3.48)): `ĉ_{x,σ}` removes one
mode creation at a time from a general flat-band Slater state, each with amplitude `μ_{qs[i]}(x)`
(on a spin match) and Koszul sign `(-1)^i`. -/
theorem generalFlatBand_siteAnnihilation_peel (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (x : Fin (M + 1)) (σ : Fin 2) (qs : List (Fin (M + 1) × Fin 2)) :
    (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)).mulVec
        (generalFlatBandSlaterState μ qs)
      = ∑ i : Fin qs.length, generalFlatBandPeelTerm μ x σ qs i := by
  induction qs with
  | nil =>
    simp only [generalFlatBandSlaterState, List.map_nil, List.prod_nil, Matrix.one_mulVec,
      List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact fermionMultiAnnihilation_mulVec_vacuum (2 * M + 1) _
  | cons q l' ih =>
    have hcons : generalFlatBandSlaterState μ (q :: l')
        = (generalFlatBandCreation μ q.1 q.2).mulVec (generalFlatBandSlaterState μ l') := by
      rw [generalFlatBandCreation_mulVec_slaterState]
    have hCAR : fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) *
          generalFlatBandCreation μ q.1 q.2
        = (if σ = q.2 then μ q.1 x else 0) • 1
          - generalFlatBandCreation μ q.1 q.2 *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) := by
      rw [eq_sub_iff_add_eq]
      exact site_annihilation_generalFlatBandCreation_anticomm M μ x q.1 σ q.2
    rw [hcons, Matrix.mulVec_mulVec, hCAR, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_sum]
    change (if σ = q.2 then μ q.1 x else 0) • generalFlatBandSlaterState μ l'
        - ∑ i : Fin l'.length,
            (generalFlatBandCreation μ q.1 q.2).mulVec (generalFlatBandPeelTerm μ x σ l' i)
      = ∑ i : Fin (l'.length + 1), generalFlatBandPeelTerm μ x σ (q :: l') i
    rw [Fin.sum_univ_succ, sub_eq_iff_eq_add, add_assoc, ← Finset.sum_add_distrib,
      Finset.sum_eq_zero (fun i _ => ?_), add_zero]
    · simp only [generalFlatBandPeelTerm, List.get_cons_zero, List.eraseIdx_cons_zero,
        Fin.val_zero, pow_zero, one_smul]
      by_cases hσ : σ = q.2
      · rw [if_pos hσ, if_pos hσ.symm]
      · rw [if_neg hσ, if_neg (fun h => hσ h.symm), zero_smul]
    · simp only [generalFlatBandPeelTerm, List.get_cons_succ', List.eraseIdx_cons_succ,
        Fin.val_succ, pow_succ]
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, generalFlatBandCreation_mulVec_slaterState,
        ← add_smul]
      rw [show (-1 : ℂ) ^ (i : ℕ) * -1 + (-1 : ℂ) ^ (i : ℕ) = 0 by ring, zero_smul]

end LatticeSystem.Fermion

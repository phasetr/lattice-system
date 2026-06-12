import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinfulVectorOperator
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBand
import LatticeSystem.Math.RayleighPosSemidefKernel
import LatticeSystem.Math.PosSemidef.Basics
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandPosSemidef

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

/-- **The double-annihilation expansion** (Tasaki's eq. (11.3.48), raw form): applying
`ĉ_{x,↓}ĉ_{x,↑}` to a Slater state expands into the double peel — the outer annihilator peels
each term of the inner peel.  Composing `generalFlatBand_siteAnnihilation_peel` twice and
pushing the second annihilator through the finite sum and the scalars. -/
theorem generalFlatBand_double_siteAnnihilation_peel (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (x : Fin (M + 1)) (σ σ' : Fin 2) (qs : List (Fin (M + 1) × Fin 2)) :
    (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ')).mulVec
      ((fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)).mulVec
        (generalFlatBandSlaterState μ qs))
      = ∑ i : Fin qs.length, ((-1 : ℂ) ^ (i : ℕ)) •
          ((if (qs.get i).2 = σ then μ (qs.get i).1 x else 0) •
            ∑ j : Fin (qs.eraseIdx i).length,
              generalFlatBandPeelTerm μ x σ' (qs.eraseIdx i) j) := by
  rw [generalFlatBand_siteAnnihilation_peel, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [generalFlatBandPeelTerm, Matrix.mulVec_smul, Matrix.mulVec_smul,
    generalFlatBand_siteAnnihilation_peel]

/-- The down-then-up site annihilation `ĉ_{x↓} ĉ_{x↑}` at general site count (the operator of
Tasaki's no-double-occupancy condition, eq. (11.3.48) left-hand side). -/
noncomputable def generalCDownUp (M : ℕ) (x : Fin (M + 1)) :
    ManyBodyOp (Fin (2 * M + 2)) :=
  fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x 1) *
    fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x 0)

/-- **`n̂_{x↑} n̂_{x↓} = (ĉ_{x↓} ĉ_{x↑})ᴴ (ĉ_{x↓} ĉ_{x↑})` at general site count**: the diagonal
double occupancy is the Gram operator of the double annihilation (general-`M` form of the
delta-chain identity, via the unified spinful CAR). -/
theorem hubbardDoubleOccupancy_eq_conjTranspose_mul_self_general (M : ℕ) (x : Fin (M + 1)) :
    hubbardDoubleOccupancy M x = (generalCDownUp M x)ᴴ * generalCDownUp M x := by
  rw [hubbardDoubleOccupancy, fermionUpNumber, fermionDownNumber, fermionMultiNumber,
    fermionMultiNumber, generalCDownUp, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, fermionMultiAnnihilation_conjTranspose]
  set cup := fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x 0)
  set cdn := fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x 1)
  set cre := fermionMultiCreation (2 * M + 1) (spinfulIndex M x 1)
  have hcd : cup * cre = -(cre * cup) := by
    have h := spinful_annihilation_creation_anticomm_general M x x 0 1
    rw [if_neg (fun hc => absurd hc.2 (by decide))] at h
    exact eq_neg_of_add_eq_zero_left h
  have haa : cup * cdn = -(cdn * cup) :=
    eq_neg_of_add_eq_zero_left
      (fermionMultiAnnihilation_anticomm_of_ne (spinfulIndex_up_ne_down M x x))
  have hmid : cup * (cre * cdn) = cre * (cdn * cup) := by
    rw [← mul_assoc, hcd, neg_mul, mul_assoc, haa, mul_neg]
    exact neg_neg _
  simp only [mul_assoc]
  rw [hmid]

/-- **Rayleigh decomposition of the general Hubbard Hamiltonian** (real `U`): the expectation
splits into the kinetic part and `U` times the summed double-occupancy expectations. -/
theorem hubbardHamiltonian_rayleighOnVec_decompose_general (M : ℕ)
    (t : Fin (M + 1) → Fin (M + 1) → ℂ) (U : ℝ)
    (v : (Fin (2 * M + 2) → Fin 2) → ℂ) :
    rayleighOnVec (hubbardHamiltonian M t (U : ℂ)) v =
      rayleighOnVec (hubbardKinetic M t) v
        + U * ∑ x : Fin (M + 1), rayleighOnVec (hubbardDoubleOccupancy M x) v := by
  unfold hubbardHamiltonian hubbardOnSiteInteraction
  rw [rayleighOnVec_add_matrix, rayleighOnVec_sum]
  simp only [rayleighOnVec_real_smul]
  rw [← Finset.mul_sum]
  rfl

/-- **Conjugate transpose of a smeared annihilation operator**: `(Ĉ_σ(φ))ᴴ = Ĉ†_σ(φ̄)` — the
adjoint of the `φ`-smeared annihilator creates the conjugated state (the Gram-form input for the
kinetic positivity from `T.PosSemidef`). -/
theorem spinfulAnnihilationFromVector_conjTranspose (M : ℕ)
    (φ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    (spinfulAnnihilationFromVector M φ σ)ᴴ = spinfulCreationFromVector M (star φ) σ := by
  unfold spinfulAnnihilationFromVector spinfulCreationFromVector
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_smul, fermionMultiAnnihilation_conjTranspose]
  rfl

/-- Expansion of the normal-ordered product `Ĉ†_σ(φ)·Ĉ_σ(ψ)` into the double sum of sitewise
`c†c` hopping terms (the Gram building block of the kinetic operator). -/
theorem spinfulCreation_mul_annihilationFromVector_expand (M : ℕ)
    (φ ψ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    spinfulCreationFromVector M φ σ * spinfulAnnihilationFromVector M ψ σ
      = ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), (φ i * ψ j) •
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
  simp only [spinfulCreationFromVector, spinfulAnnihilationFromVector, Finset.sum_mul,
    Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [mul_comm (ψ j) (φ i)]

open scoped ComplexOrder in
/-- **The kinetic operator is positive-semidefinite when the hopping matrix is**
(Tasaki §11.3.4, the frustration-free structure for a general flat band): writing
`T = C·C` with `C` positive-semidefinite (hence Hermitian, repo A.6), the kinetic operator
factors as `Σ_σ Σ_k (Ĉ_σ(C_k))ᴴ (Ĉ_σ(C_k))` — a sum of Gram operators, each PSD. -/
theorem hubbardKinetic_posSemidef_of_posSemidef (M : ℕ)
    (t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (ht : t.PosSemidef) :
    (hubbardKinetic M t).PosSemidef := by
  obtain ⟨C, hC, hTC⟩ := LatticeSystem.Math.exists_posSemidef_sq_eq_of_posSemidef ht
  have key : hubbardKinetic M t
      = ∑ σ : Fin 2, ∑ k : Fin (M + 1),
          (spinfulAnnihilationFromVector M (fun j => C k j) σ)ᴴ *
            spinfulAnnihilationFromVector M (fun j => C k j) σ := by
    unfold hubbardKinetic
    refine Finset.sum_congr rfl fun σ _ => ?_
    symm
    calc ∑ k : Fin (M + 1),
            (spinfulAnnihilationFromVector M (fun j => C k j) σ)ᴴ *
              spinfulAnnihilationFromVector M (fun j => C k j) σ
        = ∑ k : Fin (M + 1), ∑ i : Fin (M + 1), ∑ j : Fin (M + 1),
            (star (C k i) * C k j) •
              (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
                fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [spinfulAnnihilationFromVector_conjTranspose,
            spinfulCreation_mul_annihilationFromVector_expand]
          simp only [Pi.star_apply]
      _ = ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), ∑ k : Fin (M + 1),
            (star (C k i) * C k j) •
              (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
                fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), t i j •
              (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
                fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_smul]
          congr 1
          have htij : t i j = ∑ k : Fin (M + 1), star (C k i) * C k j := by
            have : t i j = (C * C) i j := by rw [hTC]
            rw [this, Matrix.mul_apply]
            exact Finset.sum_congr rfl fun k _ => by rw [hC.isHermitian.apply i k]
          rw [htij]
  rw [key]
  exact Matrix.posSemidef_sum _ fun σ _ =>
    Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_conjTranspose_mul_self _

open scoped ComplexOrder in
/-- **No double occupancy for a general flat-band ground state** (Tasaki eq. (11.3.12), general
form): for a positive-semidefinite hopping `T` and `U > 0`, any vector with vanishing Hamiltonian
expectation satisfies `n̂_{x↑} n̂_{x↓} v = 0` at every site `x`.  The Rayleigh expectation splits
into the (PSD) kinetic part and `U` times the summed (PSD) double-occupancy expectations; all are
nonnegative and sum to zero, so each double-occupancy term vanishes, and the PSD kernel kills the
operator on `v`. -/
theorem generalFlatBand_groundState_doubleOccupancy_mulVec_eq_zero (M : ℕ)
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) v = 0) (x : Fin (M + 1)) :
    (hubbardDoubleOccupancy M x).mulVec v = 0 := by
  have hkin_nonneg : 0 ≤ rayleighOnVec (hubbardKinetic M T) v :=
    (hubbardKinetic_posSemidef_of_posSemidef M T hT).re_dotProduct_nonneg v
  have hint_nonneg : ∀ x' : Fin (M + 1),
      0 ≤ rayleighOnVec (hubbardDoubleOccupancy M x') v :=
    fun x' => (hubbardDoubleOccupancy_posSemidef M x').re_dotProduct_nonneg v
  have hdec := hubbardHamiltonian_rayleighOnVec_decompose_general M T U v
  rw [hv] at hdec
  have hInt : (0 : ℝ) ≤ ∑ x' : Fin (M + 1), rayleighOnVec (hubbardDoubleOccupancy M x') v :=
    Finset.sum_nonneg (fun x' _ => hint_nonneg x')
  have hIntZero : (∑ x' : Fin (M + 1), rayleighOnVec (hubbardDoubleOccupancy M x') v) = 0 := by
    nlinarith [mul_nonneg hU.le hInt, hkin_nonneg, hdec]
  have hterm : rayleighOnVec (hubbardDoubleOccupancy M x) v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x' _ => hint_nonneg x')).mp hIntZero x
      (Finset.mem_univ x)
  exact posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero
    (hubbardDoubleOccupancy_posSemidef M x) hterm

open scoped ComplexOrder in
/-- **`ĉ_{x↓} ĉ_{x↑} v = 0`** for any general flat-band ground state `v` (the operator form of the
no-double-occupancy condition used in eq. (11.3.48)): from `n̂_{x↑} n̂_{x↓} v = 0` and the Gram
identity, by the positive-semidefinite kernel. -/
theorem generalFlatBand_groundState_doubleAnnihilation_mulVec_eq_zero (M : ℕ)
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) v = 0) (x : Fin (M + 1)) :
    (generalCDownUp M x).mulVec v = 0 := by
  have hdo := generalFlatBand_groundState_doubleOccupancy_mulVec_eq_zero M T U hT hU hv x
  rw [hubbardDoubleOccupancy_eq_conjTranspose_mul_self_general] at hdo
  exact conjTranspose_mul_self_mulVec_eq_zero hdo

open scoped ComplexOrder in
/-- **`ĉ_{x↓} ĉ_{x↑} Φ = 0` for any vector in the ground submodule**: the ground submodule sits
in the kernel of `Ĥ`, so its Rayleigh expectation vanishes and the no-double-occupancy kill
applies (Tasaki §11.3.4 — the eq.-(11.3.48) input phrased directly for ground states). -/
theorem generalCDownUp_mulVec_eq_zero_of_mem_groundSubmodule
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (x : Fin (M + 1)) :
    (generalCDownUp M x).mulVec Φ = 0 := by
  have hker : (hubbardHamiltonian M T (U : ℂ)).mulVec Φ = 0 := by
    have h := (Submodule.mem_inf.mp hΦ).1
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    exact h
  have hray : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) Φ = 0 := by
    rw [rayleighOnVec, hker, dotProduct_zero, Complex.zero_re]
  exact generalFlatBand_groundState_doubleAnnihilation_mulVec_eq_zero M T U hT hU hray x

/-- **Gram-sum factorization of the kinetic operator** for a factored hopping `T = Cᴴ·C`:
`hubbardKinetic M (Cᴴ·C) = Σ_σ Σ_k (Ĉ_σ(C_k))ᴴ (Ĉ_σ(C_k))`, the rows `C_k` of `C` smeared into
mode operators.  The general-`C` form of the kinetic-PSD factorization (no Hermitian assumption on
`C`); the engine for "ground state ⟹ annihilated by every row mode" toward eq. (11.3.46). -/
theorem hubbardKinetic_conjTranspose_mul_self_eq_gram_sum (M : ℕ)
    (C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) :
    hubbardKinetic M (Cᴴ * C)
      = ∑ σ : Fin 2, ∑ k : Fin (M + 1),
          (spinfulAnnihilationFromVector M (fun j => C k j) σ)ᴴ *
            spinfulAnnihilationFromVector M (fun j => C k j) σ := by
  unfold hubbardKinetic
  refine Finset.sum_congr rfl fun σ _ => ?_
  symm
  calc ∑ k : Fin (M + 1),
          (spinfulAnnihilationFromVector M (fun j => C k j) σ)ᴴ *
            spinfulAnnihilationFromVector M (fun j => C k j) σ
      = ∑ k : Fin (M + 1), ∑ i : Fin (M + 1), ∑ j : Fin (M + 1),
          (star (C k i) * C k j) •
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [spinfulAnnihilationFromVector_conjTranspose,
          spinfulCreation_mul_annihilationFromVector_expand]
        simp only [Pi.star_apply]
    _ = ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), ∑ k : Fin (M + 1),
          (star (C k i) * C k j) •
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), (Cᴴ * C) i j •
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_smul]
        congr 1

open scoped ComplexOrder in
/-- **Ground-state annihilation by every row mode**: if the kinetic Rayleigh expectation of `v`
vanishes (for a factored hopping `T = Cᴴ·C`), then each smeared annihilation `Ĉ_σ(C_k) v = 0`.
Each Gram term `(Ĉ_σ(C_k))ᴴ Ĉ_σ(C_k)` is PSD with nonnegative expectation; they sum to zero, so
each vanishes, and the PSD kernel kills `Ĉ_σ(C_k) v`.  This is the operative consequence of the
flat-band ground condition toward eq. (11.3.46). -/
theorem spinfulAnnihilationFromVector_mulVec_eq_zero_of_kinetic_rayleigh_zero (M : ℕ)
    (C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (h : rayleighOnVec (hubbardKinetic M (Cᴴ * C)) v = 0) (k : Fin (M + 1)) (σ : Fin 2) :
    (spinfulAnnihilationFromVector M (fun j => C k j) σ).mulVec v = 0 := by
  have hnonneg : ∀ (σ' : Fin 2) (k' : Fin (M + 1)),
      0 ≤ rayleighOnVec
        ((spinfulAnnihilationFromVector M (fun j => C k' j) σ')ᴴ *
          spinfulAnnihilationFromVector M (fun j => C k' j) σ') v :=
    fun σ' k' => (Matrix.posSemidef_conjTranspose_mul_self _).re_dotProduct_nonneg v
  rw [hubbardKinetic_conjTranspose_mul_self_eq_gram_sum, rayleighOnVec_sum] at h
  simp only [rayleighOnVec_sum] at h
  have hσ : (∑ k' : Fin (M + 1), rayleighOnVec
      ((spinfulAnnihilationFromVector M (fun j => C k' j) σ)ᴴ *
        spinfulAnnihilationFromVector M (fun j => C k' j) σ) v) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun σ' _ => Finset.sum_nonneg fun k' _ => hnonneg σ' k')).mp h σ (Finset.mem_univ σ)
  have hterm : rayleighOnVec
      ((spinfulAnnihilationFromVector M (fun j => C k j) σ)ᴴ *
        spinfulAnnihilationFromVector M (fun j => C k j) σ) v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k' _ => hnonneg σ k')).mp hσ k (Finset.mem_univ k)
  have hker := posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero
    (Matrix.posSemidef_conjTranspose_mul_self _) hterm
  exact conjTranspose_mul_self_mulVec_eq_zero hker

/-- `Ĉ_σ` is additive in its single-particle state: `Ĉ_σ(φ + ψ) = Ĉ_σ(φ) + Ĉ_σ(ψ)`. -/
theorem spinfulAnnihilationFromVector_add (M : ℕ) (φ ψ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    spinfulAnnihilationFromVector M (φ + ψ) σ
      = spinfulAnnihilationFromVector M φ σ + spinfulAnnihilationFromVector M ψ σ := by
  unfold spinfulAnnihilationFromVector
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by rw [Pi.add_apply, add_smul]

/-- `Ĉ_σ` is homogeneous in its single-particle state: `Ĉ_σ(a • φ) = a • Ĉ_σ(φ)`. -/
theorem spinfulAnnihilationFromVector_smul (M : ℕ) (a : ℂ) (φ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    spinfulAnnihilationFromVector M (a • φ) σ = a • spinfulAnnihilationFromVector M φ σ := by
  unfold spinfulAnnihilationFromVector
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [Pi.smul_apply, smul_eq_mul, ← smul_smul]

/-- `Ĉ_σ(0) = 0`. -/
@[simp] theorem spinfulAnnihilationFromVector_zero (M : ℕ) (σ : Fin 2) :
    spinfulAnnihilationFromVector M (0 : Fin (M + 1) → ℂ) σ = 0 := by
  unfold spinfulAnnihilationFromVector
  exact Finset.sum_eq_zero fun x _ => by rw [Pi.zero_apply, zero_smul]

/-- **Annihilation extends to any linear combination of states**: if `Ĉ_σ(φ_i) v = 0` for every
`i` in a finite family, then `Ĉ_σ(Σ_i a_i φ_i) v = 0` for any coefficients `a_i`. -/
theorem spinfulAnnihilationFromVector_linearCombination_mulVec_eq_zero (M : ℕ) {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) (φ : ι → Fin (M + 1) → ℂ) (σ : Fin 2)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (h : ∀ i ∈ s, (spinfulAnnihilationFromVector M (φ i) σ).mulVec v = 0) :
    (spinfulAnnihilationFromVector M (∑ i ∈ s, a i • φ i) σ).mulVec v = 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, spinfulAnnihilationFromVector_add,
      spinfulAnnihilationFromVector_smul, Matrix.add_mulVec, Matrix.smul_mulVec,
      h i (Finset.mem_insert_self i s),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)), smul_zero, add_zero]

open scoped ComplexOrder in
/-- **A flat-band ground state is annihilated by every row-space mode**: for `T = Cᴴ·C` and a
vector with vanishing kinetic Rayleigh expectation, `Ĉ_σ(Σ_k a_k C_k) v = 0` for any coefficients
`a` — i.e. `Ĉ_σ(w) v = 0` for every `w` in the row span of `C` (which is the range of `T`, the
orthocomplement of the flat band).  Combines the per-row kill with the linearity of `Ĉ_σ`. -/
theorem spinfulAnnihilation_rowSpan_mulVec_eq_zero (M : ℕ)
    (C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (h : rayleighOnVec (hubbardKinetic M (Cᴴ * C)) v = 0) (σ : Fin 2)
    (a : Fin (M + 1) → ℂ) :
    (spinfulAnnihilationFromVector M (∑ k : Fin (M + 1), a k • (fun j => C k j)) σ).mulVec v = 0 :=
  spinfulAnnihilationFromVector_linearCombination_mulVec_eq_zero M Finset.univ a
    (fun k => fun j => C k j) σ
    (fun k _ => spinfulAnnihilationFromVector_mulVec_eq_zero_of_kinetic_rayleigh_zero M C h k σ)

open scoped ComplexOrder in
/-- **The kinetic Rayleigh expectation vanishes on a flat-band ground state**: for `T` PSD and
`U > 0`, if the full Hamiltonian expectation is zero then so is the kinetic one (the kinetic and
the `U`-weighted double-occupancy parts are both nonnegative and sum to zero). -/
theorem hubbardKinetic_rayleigh_zero_of_groundState (M : ℕ)
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) v = 0) :
    rayleighOnVec (hubbardKinetic M T) v = 0 := by
  have hkin_nonneg : 0 ≤ rayleighOnVec (hubbardKinetic M T) v :=
    (hubbardKinetic_posSemidef_of_posSemidef M T hT).re_dotProduct_nonneg v
  have hint_nonneg : ∀ x' : Fin (M + 1),
      0 ≤ rayleighOnVec (hubbardDoubleOccupancy M x') v :=
    fun x' => (hubbardDoubleOccupancy_posSemidef M x').re_dotProduct_nonneg v
  have hInt : (0 : ℝ) ≤ ∑ x' : Fin (M + 1), rayleighOnVec (hubbardDoubleOccupancy M x') v :=
    Finset.sum_nonneg (fun x' _ => hint_nonneg x')
  have hdec := hubbardHamiltonian_rayleighOnVec_decompose_general M T U v
  rw [hv] at hdec
  nlinarith [mul_nonneg hU.le hInt, hkin_nonneg, hdec]

open scoped ComplexOrder in
/-- **A flat-band ground state is annihilated by every range-`T` mode** (the operative content of
eq. (11.3.46)): for `T` PSD and `U > 0`, any vector with vanishing Hamiltonian expectation is
killed by `Ĉ_σ(T_k)` summed against any coefficients — i.e. by `Ĉ_σ(w)` for every `w` in the
range of `T = (ker T)^⊥`.  Factoring `T = Cᴴ·C` (positive square root), the kinetic Rayleigh
vanishes, so each Gram mode kills `v`, and the row span of `C` is the range of `T`. -/
theorem spinfulAnnihilation_rangeT_mulVec_eq_zero_of_groundState (M : ℕ)
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) v = 0) (σ : Fin 2) :
    ∃ C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ, T = Cᴴ * C ∧
      ∀ a : Fin (M + 1) → ℂ,
        (spinfulAnnihilationFromVector M (∑ k : Fin (M + 1), a k • (fun j => C k j)) σ).mulVec v
          = 0 := by
  obtain ⟨C, hC, hTC⟩ := LatticeSystem.Math.exists_posSemidef_sq_eq_of_posSemidef hT
  have hTCH : T = Cᴴ * C := by rw [hTC, hC.isHermitian.eq]
  refine ⟨C, hTCH, fun a => ?_⟩
  have hkin : rayleighOnVec (hubbardKinetic M (Cᴴ * C)) v = 0 := by
    rw [← hTCH]; exact hubbardKinetic_rayleigh_zero_of_groundState M T U hT hU hv
  exact spinfulAnnihilation_rowSpan_mulVec_eq_zero M C hkin σ a

/-- The Hamiltonian Rayleigh expectation vanishes on any ground-submodule vector (it lies in the
kernel of `Ĥ`). -/
theorem hamiltonian_rayleigh_zero_of_mem_groundSubmodule
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) Φ = 0 := by
  have hker : (hubbardHamiltonian M T (U : ℂ)).mulVec Φ = 0 := by
    have h := (Submodule.mem_inf.mp hΦ).1
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    exact h
  rw [rayleighOnVec, hker, dotProduct_zero, Complex.zero_re]

open scoped ComplexOrder in
/-- **A ground-submodule vector is annihilated by every range-`T` mode** (eq. (11.3.46) premise,
packaged for the ground submodule): factoring `T = Cᴴ·C`, every `Ĉ_σ(Σ a_k C_k)` kills `Φ`. -/
theorem spinfulAnnihilation_rangeT_mulVec_eq_zero_of_mem_groundSubmodule
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (σ : Fin 2) :
    ∃ C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ, T = Cᴴ * C ∧
      ∀ a : Fin (M + 1) → ℂ,
        (spinfulAnnihilationFromVector M (∑ k : Fin (M + 1), a k • (fun j => C k j)) σ).mulVec Φ
          = 0 :=
  spinfulAnnihilation_rangeT_mulVec_eq_zero_of_groundState M T U hT hU
    (hamiltonian_rayleigh_zero_of_mem_groundSubmodule T U hΦ) σ

/-- **A nonzero-eigenvalue eigenvector lies in the range of the matrix** (`u = T·(λ⁻¹ u)`): the
single-particle modes orthogonal to the flat band `ker T` are exactly the range of `T`, the source
of the complement creation operators in the full Fock basis (toward eq. (11.3.46)). -/
theorem mem_range_mulVec_of_eigenvalue_ne_zero
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) {lam : ℂ} (hlam : lam ≠ 0)
    {u : Fin (M + 1) → ℂ} (hu : T.mulVec u = lam • u) :
    ∃ w : Fin (M + 1) → ℂ, T.mulVec w = u :=
  ⟨lam⁻¹ • u, by rw [Matrix.mulVec_smul, hu, smul_smul, inv_mul_cancel₀ hlam, one_smul]⟩

/-- **Conjugate transpose of a smeared creation operator**: `(Ĉ†_σ(φ))ᴴ = Ĉ_σ(φ̄)` — the adjoint
of the `φ`-smeared creator annihilates the conjugated state (companion to
`spinfulAnnihilationFromVector_conjTranspose`). -/
theorem spinfulCreationFromVector_conjTranspose (M : ℕ)
    (φ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    (spinfulCreationFromVector M φ σ)ᴴ = spinfulAnnihilationFromVector M (star φ) σ := by
  unfold spinfulCreationFromVector spinfulAnnihilationFromVector
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_smul, fermionMultiCreation_conjTranspose]
  rfl

/-- **A zero-eigenvalue eigenvector lies in the flat band `ker T`**: the spectral basis splits the
single-particle space into the flat band (zero eigenvalues) and its orthocomplement `range T`
(nonzero eigenvalues), the basis for the full Fock decomposition toward eq. (11.3.46). -/
theorem eigenvectorBasis_mem_ker_of_eigenvalue_eq_zero
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) (j : Fin (M + 1))
    (hj : hT.eigenvalues j = 0) :
    T.mulVec (⇑(hT.eigenvectorBasis j)) = 0 := by
  rw [hT.mulVec_eigenvectorBasis, hj]
  exact zero_smul _ _

end LatticeSystem.Fermion

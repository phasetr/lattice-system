import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandMuTransport

/-!
# Spin-configuration representation (Tasaki §11.3.4, eq. 11.3.47, toward Theorem 11.17)

After the transport to the special basis (PR6), a flat-band ground state at filling `D₀` lies in the
`μ`-Slater Fock submodule.  Tasaki's eq. (11.3.47) refines this: using `ĉ_{z,↓}ĉ_{z,↑}|Φ⟩ = 0` for
`z ∈ I` (from `Ĥ_int|Φ⟩ = 0`), there can be no double occupancy of the `â†_{μ_z}` modes, so the
ground
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

/-- **The site-dual CAR on the index set `I`** (Tasaki §11.3.4): for `z, z' ∈ I`, the special
basis's
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

/-- **The index-mode number operator** `n̂^μ_{z,σ} = â†_{μ_z,σ}·ĉ_{z,σ}` counts (up to the scale
`μ_z(z)`) the occupation of the special-basis index mode `(z, σ)`, using the site annihilator `ĉ_z`
as the dual of `â†_{μ_z}` on the index set `I`. -/
noncomputable def muNumberOp (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (z : Fin (M + 1)) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * M + 2)) :=
  generalFlatBandCreation μ z σ * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ)

/-- **The index-mode number-operator/creation commutation**:
`n̂^μ_{z,σ}·â†_{μ_{z'},τ} = δ_{στ}δ_{zz'}μ_z(z)·â†_{μ_{z'},τ} + â†_{μ_{z'},τ}·n̂^μ_{z,σ}`
(for `z, z' ∈ I`).  From the localized site-dual CAR and the creation–creation anticommutation;
mirrors `eigenNumberOp_mul_creation` of the eq. (11.3.46) machinery. -/
theorem muNumberOp_mul_creation
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {z z' : Fin (M + 1)} (hz : z ∈ I) (hz' : z' ∈ I) (σ τ : Fin 2) :
    muNumberOp μ z σ * generalFlatBandCreation μ z' τ
      = (if σ = τ ∧ z = z' then μ z z else 0) • generalFlatBandCreation μ z' τ
        + generalFlatBandCreation μ z' τ * muNumberOp μ z σ := by
  have hdual : fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ)
        * generalFlatBandCreation μ z' τ
      = (if σ = τ ∧ z = z' then μ z z else 0) • 1
        - generalFlatBandCreation μ z' τ
          * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ) := by
    rw [eq_sub_iff_add_eq]
    exact site_annihilation_generalFlatBandCreation_anticomm_localized hbasis hz hz' σ τ
  have hcc : generalFlatBandCreation μ z σ * generalFlatBandCreation μ z' τ
      = - (generalFlatBandCreation μ z' τ * generalFlatBandCreation μ z σ) :=
    eq_neg_of_add_eq_zero_left
      (spinfulFromVector_creation_creation_anticomm M (μ z) (μ z') σ τ)
  have hδ : (if σ = τ ∧ z = z' then μ z z else 0) • generalFlatBandCreation μ z σ
      = (if σ = τ ∧ z = z' then μ z z else 0) • generalFlatBandCreation μ z' τ := by
    by_cases h : σ = τ ∧ z = z'
    · rw [h.1, h.2]
    · rw [if_neg h, zero_smul, zero_smul]
  rw [muNumberOp, Matrix.mul_assoc, hdual, mul_sub, mul_smul_comm, Matrix.mul_one,
    ← Matrix.mul_assoc, hcc, Matrix.neg_mul, sub_neg_eq_add, hδ, Matrix.mul_assoc]

/-- **The index-mode number operator is diagonal in the `μ`-Slater states**:
`n̂^μ_{z,σ}|qs⟩ = μ_z(z)·(count of (z,σ) in qs)·|qs⟩` (for a list `qs` of index modes, `z ∈ I`).
List induction via the commutation, down to `n̂^μ_{z,σ}|vac⟩ = 0`. -/
theorem muNumberOp_mulVec_generalFlatBandSlaterState
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {z : Fin (M + 1)} (hz : z ∈ I) (σ : Fin 2) (qs : List (Fin (M + 1) × Fin 2))
    (hqs : ∀ q ∈ qs, q.1 ∈ I) :
    (muNumberOp μ z σ).mulVec (generalFlatBandSlaterState μ qs)
      = (μ z z * (qs.count (z, σ) : ℂ)) • generalFlatBandSlaterState μ qs := by
  induction qs with
  | nil =>
    rw [muNumberOp]
    simp only [generalFlatBandSlaterState, List.map_nil, List.prod_nil, Matrix.one_mulVec,
      List.count_nil, Nat.cast_zero, mul_zero, zero_smul]
    rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_vacuum, Matrix.mulVec_zero]
  | cons q qs' ih =>
    obtain ⟨q1, q2⟩ := q
    have hcons : generalFlatBandSlaterState μ ((q1, q2) :: qs')
        = (generalFlatBandCreation μ q1 q2).mulVec (generalFlatBandSlaterState μ qs') :=
      (generalFlatBandCreation_mulVec_slaterState μ q1 q2 qs').symm
    rw [hcons, Matrix.mulVec_mulVec,
      muNumberOp_mul_creation hbasis hz (hqs (q1, q2) List.mem_cons_self) σ q2,
      Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      ih (fun q' hq' => hqs q' (List.mem_cons_of_mem _ hq')), Matrix.mulVec_smul, ← add_smul]
    congr 1
    rw [List.count_cons]
    simp only [beq_iff_eq]
    push_cast
    by_cases h : (z, σ) = (q1, q2)
    · rw [if_pos ⟨(Prod.ext_iff.mp h).2, (Prod.ext_iff.mp h).1⟩, if_pos h.symm]
      ring
    · rw [if_neg (fun hc => h (Prod.ext hc.2 hc.1)), if_neg (fun he => h he.symm)]
      ring

/-- **The double index-mode number operator equals the doubled creation times the site
double-annihilation**: `n̂^μ_{z,↑}·n̂^μ_{z,↓} = â†_{μ_z,↑}·â†_{μ_z,↓}·(ĉ_{z,↓}ĉ_{z,↑})`.  Moving the
up-spin site annihilator past the down-spin mode creator (cross-spin, anticommute) and the two site
annihilators past each other.  (Spins: `↑ = 0`, `↓ = 1`.) -/
theorem muNumberOp_mul_eq_creation_creation_cdownup
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {z : Fin (M + 1)} (hz : z ∈ I) :
    muNumberOp μ z 0 * muNumberOp μ z 1
      = generalFlatBandCreation μ z 0 * generalFlatBandCreation μ z 1 * generalCDownUp M z := by
  have hcross : fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 0)
        * generalFlatBandCreation μ z 1
      = - (generalFlatBandCreation μ z 1
          * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 0)) := by
    apply eq_neg_of_add_eq_zero_left
    have h := site_annihilation_generalFlatBandCreation_anticomm_localized hbasis hz hz 0 1
    rwa [if_neg (fun hc => absurd hc.1 (by decide)), zero_smul] at h
  have hann : fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 0)
        * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 1)
      = - generalCDownUp M z := by
    rw [generalCDownUp]
    exact eq_neg_of_add_eq_zero_left
      (fermionMultiAnnihilation_anticomm_of_ne (spinfulIndex_up_ne_down M z z))
  calc muNumberOp μ z 0 * muNumberOp μ z 1
      = generalFlatBandCreation μ z 0
          * (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 0)
              * generalFlatBandCreation μ z 1)
          * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 1) := by
        rw [muNumberOp, muNumberOp]; noncomm_ring
    _ = generalFlatBandCreation μ z 0
          * (- (generalFlatBandCreation μ z 1
              * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 0)))
          * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 1) := by rw [hcross]
    _ = - (generalFlatBandCreation μ z 0 * generalFlatBandCreation μ z 1
          * (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 0)
              * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 1))) := by noncomm_ring
    _ = - (generalFlatBandCreation μ z 0 * generalFlatBandCreation μ z 1
          * (- generalCDownUp M z)) := by rw [hann]
    _ = generalFlatBandCreation μ z 0 * generalFlatBandCreation μ z 1 * generalCDownUp M z := by
        noncomm_ring

open scoped ComplexOrder in
/-- **No double occupancy of the index modes**: for a flat-band ground state `Φ`, the double
index-mode number operator kills it, `n̂^μ_{z,↑}·n̂^μ_{z,↓}·Φ = 0` (`z ∈ I`).  From the operator
identity and `ĉ_{z,↓}ĉ_{z,↑}Φ = 0` (the `Ĥ_int|Φ⟩ = 0` zero-energy condition). -/
theorem muNumberOp_double_mulVec_eq_zero_of_mem_groundSubmodule
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U) {z : Fin (M + 1)} (hz : z ∈ I)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    (muNumberOp μ z 0 * muNumberOp μ z 1).mulVec Φ = 0 := by
  rw [muNumberOp_mul_eq_creation_creation_cdownup hbasis hz, ← Matrix.mulVec_mulVec,
    generalCDownUp_mulVec_eq_zero_of_mem_groundSubmodule T U hT hU hΦ z, Matrix.mulVec_zero]

end LatticeSystem.Fermion

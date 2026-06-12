import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandOccBasis

/-!
# The spectral eigenbasis as a single-particle basis (Tasaki §11.3.4, toward eq. (11.3.46))

For a Hermitian hopping matrix `T`, the orthonormal eigenbasis `T.IsHermitian.eigenvectorBasis`
(on `EuclideanSpace ℂ (Fin (M+1))`) transports to a `Module.Basis` of the plain coordinate space
`Fin (M+1) → ℂ`, on which the general occupation basis (`GeneralFlatBandOccBasis.lean`) is built.
Its orthonormality yields the **dual canonical anticommutation relation**
`{Ĉ_σ(ē_j), Ĉ†_τ(e_k)} = δ_{jk}δ_{στ}·1`, the exact occupation-detection algebra used to peel a flat
band ground state into its zero-eigenvalue (flat-band) modes (eq. (11.3.46)).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.46).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {M : ℕ}

/-- The orthonormal eigenbasis of a Hermitian `T`, transported from `EuclideanSpace ℂ (Fin (M+1))`
to a `Module.Basis` of the plain coordinate space `Fin (M+1) → ℂ`. -/
noncomputable def eigenbasisAsBasis {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) :
    Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ) :=
  hT.eigenvectorBasis.toBasis.map (WithLp.linearEquiv 2 ℂ (Fin (M + 1) → ℂ))

/-- The `i`-th transported basis vector is the underlying coordinate function of the `i`-th
eigenvector. -/
theorem eigenbasisAsBasis_apply {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian)
    (i : Fin (M + 1)) :
    (eigenbasisAsBasis hT i : Fin (M + 1) → ℂ)
      = (⇑(hT.eigenvectorBasis i) : Fin (M + 1) → ℂ) := by
  rw [eigenbasisAsBasis, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis]
  rfl

/-- **Orthonormality of the eigenbasis, in coordinate form**:
`∑_x conj(e_j(x))·e_k(x) = δ_{jk}`. -/
theorem eigenbasisAsBasis_orthonormal_sum
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) (j k : Fin (M + 1)) :
    (∑ x : Fin (M + 1),
        star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)
          * (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) x)
      = if j = k then (1 : ℂ) else 0 := by
  have ho := hT.eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at ho
  have hjk := ho j k
  rw [PiLp.inner_apply] at hjk
  rw [← hjk]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [RCLike.inner_apply]
  simp only [starRingEnd_apply, eigenbasisAsBasis_apply]
  ring

/-- **The dual canonical anticommutation relation in the eigenbasis**:
`{Ĉ_σ(ē_j), Ĉ†_τ(e_k)} = δ_{jk}·δ_{στ}·1`.  The smeared CAR
(`spinfulFromVector_annihilation_creation_anticomm`) gives the coefficient
`∑_x conj(e_j(x))·e_k(x)`, which the orthonormality collapses to `δ_{jk}`.  This is the exact
occupation-detection algebra for the eq. (11.3.46) Fock-spanning step. -/
theorem eigenbasis_dual_annihilation_creation_anticomm
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) (j k : Fin (M + 1))
    (σ τ : Fin 2) :
    spinfulAnnihilationFromVector M (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ
        * spinfulCreationFromVector M (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) τ
      + spinfulCreationFromVector M (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) τ
        * spinfulAnnihilationFromVector M (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ
      = (if j = k ∧ σ = τ then (1 : ℂ) else 0) • (1 : ManyBodyOp (Fin (2 * M + 2))) := by
  rw [spinfulFromVector_annihilation_creation_anticomm M
        (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) (eigenbasisAsBasis hT k) σ τ]
  by_cases hστ : σ = τ
  · subst hστ
    have hsum : (∑ x : Fin (M + 1),
        (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) x
          * (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) x)
        = if j = k then (1 : ℂ) else 0 := by
      simpa only [Pi.star_apply] using eigenbasisAsBasis_orthonormal_sum hT j k
    rw [if_pos rfl, hsum]
    by_cases hjk : j = k <;> simp [hjk]
  · rw [if_neg hστ]
    have : ¬ (j = k ∧ σ = τ) := fun h => hστ h.2
    rw [if_neg this]

/-- The smeared annihilator kills the vacuum: `Ĉ_σ(φ)|vac⟩ = 0`. -/
theorem spinfulAnnihilationFromVector_mulVec_vacuum (φ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    (spinfulAnnihilationFromVector M φ σ).mulVec (fermionMultiVacuum (2 * M + 1)) = 0 := by
  rw [spinfulAnnihilationFromVector, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Matrix.smul_mulVec, fermionMultiAnnihilation_mulVec_vacuum, smul_zero]

/-- **The single peeled contribution** of position `i` when the eigenbasis annihilator `Ĉ_σ(ē_j)`
passes through a general mode monomial: amplitude `δ_{j,(qs[i]).1}·δ_{σ,(qs[i]).2}` (the dual CAR
Kronecker delta) and Koszul sign `(-1)^i`, leaving the monomial with the `i`-th mode removed. -/
noncomputable def eigenModePeelTerm (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (j : Fin (M + 1)) (σ : Fin 2) (qs : List (Fin (M + 1) × Fin 2)) (i : Fin qs.length) :
    (Fin (2 * M + 2) → Fin 2) → ℂ :=
  ((-1 : ℂ) ^ (i : ℕ)) •
    ((if j = (qs.get i).1 ∧ σ = (qs.get i).2 then (1 : ℂ) else 0) •
      generalModeMonomial e (qs.eraseIdx i))

/-- **The eigenbasis-annihilation peel**: `Ĉ_σ(ē_j)` removes one mode creation at a time from a
general mode monomial, each with amplitude `δ_{j,(qs[i]).1}·δ_{σ,(qs[i]).2}` and Koszul sign
`(-1)^i`.  The orthonormal-eigenbasis analogue of `generalFlatBand_siteAnnihilation_peel`. -/
theorem eigenModeAnnihilation_peel {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian)
    (j : Fin (M + 1)) (σ : Fin 2) (qs : List (Fin (M + 1) × Fin 2)) :
    (spinfulAnnihilationFromVector M
        (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ).mulVec
        (generalModeMonomial (eigenbasisAsBasis hT) qs)
      = ∑ i : Fin qs.length, eigenModePeelTerm (eigenbasisAsBasis hT) j σ qs i := by
  induction qs with
  | nil =>
    simp only [generalModeMonomial, List.map_nil, List.prod_nil, Matrix.one_mulVec,
      List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact spinfulAnnihilationFromVector_mulVec_vacuum _ σ
  | cons q l' ih =>
    have hcons : generalModeMonomial (eigenbasisAsBasis hT) (q :: l')
        = (spinfulCreationFromVector M (eigenbasisAsBasis hT q.1) q.2).mulVec
            (generalModeMonomial (eigenbasisAsBasis hT) l') := by
      rw [spinfulCreation_mulVec_generalModeMonomial]
    have hCAR : spinfulAnnihilationFromVector M
            (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ
          * spinfulCreationFromVector M (eigenbasisAsBasis hT q.1) q.2
        = (if j = q.1 ∧ σ = q.2 then (1 : ℂ) else 0) • 1
          - spinfulCreationFromVector M (eigenbasisAsBasis hT q.1) q.2
            * spinfulAnnihilationFromVector M
                (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ := by
      rw [eq_sub_iff_add_eq]
      exact eigenbasis_dual_annihilation_creation_anticomm hT j q.1 σ q.2
    rw [hcons, Matrix.mulVec_mulVec, hCAR, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_sum]
    change (if j = q.1 ∧ σ = q.2 then (1 : ℂ) else 0)
          • generalModeMonomial (eigenbasisAsBasis hT) l'
        - ∑ i : Fin l'.length,
            (spinfulCreationFromVector M (eigenbasisAsBasis hT q.1) q.2).mulVec
              (eigenModePeelTerm (eigenbasisAsBasis hT) j σ l' i)
      = ∑ i : Fin (l'.length + 1),
          eigenModePeelTerm (eigenbasisAsBasis hT) j σ (q :: l') i
    rw [Fin.sum_univ_succ, sub_eq_iff_eq_add, add_assoc, ← Finset.sum_add_distrib,
      Finset.sum_eq_zero (fun i _ => ?_), add_zero]
    · simp only [eigenModePeelTerm, List.get_cons_zero, List.eraseIdx_cons_zero,
        Fin.val_zero, pow_zero, one_smul]
      by_cases h : j = q.1 ∧ σ = q.2
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, zero_smul]
    · simp only [eigenModePeelTerm, List.get_cons_succ', List.eraseIdx_cons_succ,
        Fin.val_succ, pow_succ]
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, spinfulCreation_mulVec_generalModeMonomial,
        Prod.mk.eta, smul_smul, smul_smul, ← add_smul]
      convert zero_smul ℂ _ using 2
      ring

end LatticeSystem.Fermion

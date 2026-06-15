import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandSpinConfigRep

/-!
# Sign propagation, eqs. (11.3.48)–(11.3.49) (Tasaki §11.3.4, toward Theorem 11.17)

PR9–PR11 wrote a flat-band Hubbard ground state `Φ` as a superposition of the spin-configuration
`μ`-Slater states `flatBandSpinConfigState σ = Π_{z∈I} â†_{μ_z,σ_z}|vac⟩` (eq. (11.3.47), `σ`-form).
The next stage extracts the coefficients `C(σ)` and propagates the Marshall sign relation
`C(σ) = C(σ_{z₁↔z₂})` across directly-connected index pairs (eqs. (11.3.48)–(11.3.49)), using the
site double-annihilation `ĉ_{x,↓}ĉ_{x,↑}Φ = 0` for `x ∈ Λ∖I`.

This module begins with the **linear independence of the spin-configuration states**: distinct spin
configurations (on `I`) give distinct occupation configs, hence distinct (linearly independent)
elements of the general occupation basis.  This is what lets `C(σ)` be a well-defined coefficient
and
underlies the coefficient extraction in the sign argument.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eqs. (11.3.48)–(11.3.49).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators ComplexOrder

variable {M : ℕ}

/-- **The spin-configuration states are linearly independent**: indexed by spin configurations
`s : I → Fin 2` (extended by `0` off `I`), the states `flatBandSpinConfigState` are distinct
elements
of the general occupation basis `generalOccBasis eμ`, hence linearly independent.  This makes the
coefficients `C(σ)` of eq. (11.3.47) well-defined. -/
theorem flatBandSpinConfigState_linearIndependent
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) :
    LinearIndependent ℂ (fun s : I → Fin 2 =>
      flatBandSpinConfigState I idx eμ
        (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)) := by
  classical
  set b := generalOccBasis eμ with hb
  have hbcoe : ∀ h, (b h : (Fin (2 * M + 2) → Fin 2) → ℂ) = generalOccMonomial eμ h :=
    fun h => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) h
  set ext : (I → Fin 2) → (Fin (M + 1) → Fin 2) :=
    fun s z => if h : z ∈ I then s ⟨z, h⟩ else 0 with hext_def
  have hext : ∀ (s : I → Fin 2) (w : Fin (M + 1)) (hw : w ∈ I), ext s w = s ⟨w, hw⟩ := by
    intro s w hw
    simp only [hext_def, dif_pos hw]
  have hfun : (fun s : I → Fin 2 => flatBandSpinConfigState I idx eμ (ext s))
      = ⇑b ∘ (fun s => flatBandSpinConfigOcc I idx (ext s)) := by
    funext s
    rw [Function.comp_apply, flatBandSpinConfigState, hbcoe]
  rw [hfun]
  refine b.linearIndependent.comp _ ?_
  intro s s' heq
  funext z
  have key := congrFun heq (idx z.1, s z)
  simp only [flatBandSpinConfigOcc] at key
  rw [if_pos ⟨z.1, z.2, by rw [hext s z.1 z.2, Subtype.coe_eta]⟩] at key
  by_contra hne
  rw [if_neg ?_] at key
  · exact absurd key (by decide)
  · rintro ⟨w, hw, hwq⟩
    have hidxw : idx w = idx z.1 := (Prod.ext_iff.mp hwq).1.symm
    have hwz : w = z.1 := flatBandSpecial_idx_injOn hbasis hidx hw z.2 hidxw
    apply hne
    have hsz : s z = ext s' w := (Prod.ext_iff.mp hwq).2
    rw [hsz, hext s' w hw]
    congr 1
    exact Subtype.ext hwz

/-- The spin-configuration occupation `flatBandSpinConfigOcc` is `idx(I)`-supported: every occupied
mode lies over an index mode `idx z` (`z ∈ I`). -/
theorem flatBandSpinConfigOcc_idxSupported (I : Finset (Fin (M + 1)))
    (idx : Fin (M + 1) → Fin (M + 1)) (σ : Fin (M + 1) → Fin 2) :
    IsIdxSupported I idx (flatBandSpinConfigOcc I idx σ) := by
  intro q hq
  by_cases h : ∃ z ∈ I, q = (idx z, σ z)
  · obtain ⟨z, hz, rfl⟩ := h
    exact Finset.mem_image_of_mem idx hz
  · rw [flatBandSpinConfigOcc, if_neg h] at hq
    exact absurd hq (by decide)

/-- **The spin-configuration state is the `μ`-Slater state of its preimage list**: each
`flatBandSpinConfigState σ` equals `generalFlatBandSlaterState μ` of the preimage list of its
occupation config.  This puts the spin-config states into `μ`-Slater form, so the site
double-annihilation peel engine (`generalFlatBand_double_siteAnnihilation_peel`) applies to them. -/
theorem flatBandSpinConfigState_eq_slaterState
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2) :
    flatBandSpinConfigState I idx eμ σ
      = generalFlatBandSlaterState μ
          (flatBandSpecialPreimageList I idx (flatBandSpinConfigOcc I idx σ)) := by
  rw [flatBandSpinConfigState,
    generalOccMonomial_eq_generalFlatBandSlaterState_of_idxSupported hidx
      (flatBandSpinConfigOcc_idxSupported I idx σ)]

/-- `flatBandSpinConfigOcc` (hence `flatBandSpinConfigState`) depends only on `σ` restricted to the
index set `I`: spin functions agreeing on `I` give the same occupation. -/
theorem flatBandSpinConfigOcc_congr (I : Finset (Fin (M + 1)))
    (idx : Fin (M + 1) → Fin (M + 1)) {σ σ' : Fin (M + 1) → Fin 2}
    (h : ∀ z ∈ I, σ z = σ' z) :
    flatBandSpinConfigOcc I idx σ = flatBandSpinConfigOcc I idx σ' := by
  funext q
  simp only [flatBandSpinConfigOcc]
  refine if_congr ⟨?_, ?_⟩ rfl rfl <;>
    · rintro ⟨z, hz, hzq⟩
      exact ⟨z, hz, by rw [hzq, h z hz]⟩

/-- **Tasaki eq. (11.3.47) as an explicit `C(σ)` sum**: a flat-band Hubbard ground state is an
explicit finite linear combination `Φ = Σ_s C(s)·flatBandSpinConfigState (extend s)` of the
spin-configuration states, indexed by spin configurations `s : I → Fin 2` **on the index set `I`**
(the same index type as the linear independence `flatBandSpinConfigState_linearIndependent`, so the
`C(s)` are the genuine, comparison-ready coefficients of eqs. (11.3.47)–(11.3.48)).  From
`flatBand_groundState_mem_spinConfigStateSpan` (PR11, narrowed to `I`-configs via
`flatBandSpinConfigOcc_congr`) and `Submodule.mem_span_range_iff_exists_fun`. -/
theorem flatBand_groundState_eq_spinConfigStateSum
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    ∃ C : (I → Fin 2) → ℂ,
      Φ = ∑ s, C s • flatBandSpinConfigState I idx eμ
        (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0) := by
  classical
  set ext : (I → Fin 2) → (Fin (M + 1) → Fin 2) :=
    fun s z => if h : z ∈ I then s ⟨z, h⟩ else 0 with hext_def
  have hmem : Φ ∈ Submodule.span ℂ
      (Set.range (fun s : I → Fin 2 => flatBandSpinConfigState I idx eμ (ext s))) := by
    refine Submodule.span_mono ?_
      (flatBand_groundState_mem_spinConfigStateSpan hbasis hT U hU eμ idx hidx hΦ)
    rintro _ ⟨σ, rfl⟩
    refine ⟨fun z => σ z.1, ?_⟩
    simp only [flatBandSpinConfigState]
    congr 1
    refine flatBandSpinConfigOcc_congr I idx fun z hz => ?_
    simp only [hext_def, dif_pos hz]
  obtain ⟨C, hC⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  exact ⟨C, hC.symm⟩

/-- **The site double-annihilation of a spin-config state, in `μ`-Slater form**: `ĉ_{x,↓}ĉ_{x,↑}`
applied to `flatBandSpinConfigState σ` is the double annihilation applied to the `μ`-Slater state of
its preimage list — the form on which the proved peel engine
`generalFlatBand_double_siteAnnihilation_peel` expands it (eq. (11.3.48) left-hand side). -/
theorem flatBandSpinConfigState_cDownUp_eq_slaterDoubleAnnih
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) :
    (generalCDownUp M x).mulVec (flatBandSpinConfigState I idx eμ σ)
      = (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x 1)).mulVec
          ((fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x 0)).mulVec
            (generalFlatBandSlaterState μ
              (flatBandSpecialPreimageList I idx (flatBandSpinConfigOcc I idx σ)))) := by
  rw [flatBandSpinConfigState_eq_slaterState hidx, generalCDownUp, ← Matrix.mulVec_mulVec]

/-- **Tasaki eq. (11.3.48), `C(σ)`-weighted vanishing**: for the explicit coefficient expansion
`Φ = Σ_s C(s)·flatBandSpinConfigState (extend s)` (PR13), the site double-annihilation
`ĉ_{x,↓}ĉ_{x,↑}`
kills `Φ` (the zero-energy condition), so the `C(σ)`-weighted sum of double-annihilated spin-config
states vanishes for **every** site `x` — in particular `x ∈ Λ∖I`, where the connectivity data
`μ_z(x)` enters via the peel engine. -/
theorem flatBand_cDownUp_spinConfigSum_eq_zero
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (C : (I → Fin 2) → ℂ)
    (hsum : Φ = ∑ s, C s • flatBandSpinConfigState I idx eμ
      (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))
    (x : Fin (M + 1)) :
    ∑ s, C s • (generalCDownUp M x).mulVec
        (flatBandSpinConfigState I idx eμ (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)) = 0 := by
  have hz := generalCDownUp_mulVec_eq_zero_of_mem_groundSubmodule T U hT hU hΦ x
  rw [hsum, Matrix.mulVec_sum] at hz
  simp only [Matrix.mulVec_smul] at hz
  exact hz

/-- **Site annihilation kills a `μ`-Slater state with no matching-spin connected mode**: if every
mode of `qs` either has zero amplitude `μ_{q.1}(x) = 0` at the site `x` or carries the wrong spin
`q.2 ≠ σ`, then `ĉ_{x,σ}|qs⟩ = 0`.  (Every peel term vanishes; the general analogue of the Theorem
11.11 `flatBand_siteAnnihilation_eq_zero`.) -/
theorem generalFlatBand_siteAnnihilation_eq_zero (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (x : Fin (M + 1)) (σ : Fin 2) (qs : List (Fin (M + 1) × Fin 2))
    (h : ∀ q ∈ qs, μ q.1 x = 0 ∨ q.2 ≠ σ) :
    (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)).mulVec
        (generalFlatBandSlaterState μ qs) = 0 := by
  rw [generalFlatBand_siteAnnihilation_peel]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [generalFlatBandPeelTerm]
  rcases h (qs.get i) (List.get_mem qs i) with h0 | hne
  · rw [h0, ite_self, zero_smul, smul_zero]
  · rw [if_neg hne, zero_smul, smul_zero]

/-- **The site double-annihilation kills a spin-config state disconnected from the site**: if every
index `z ∈ I` has zero amplitude `μ_z(x) = 0` at the site `x` (so `x` connects to no index mode),
then `ĉ_{x,↓}ĉ_{x,↑}|s⟩ = 0`.  (The inner `ĉ_{x,↑}` already annihilates the state via
`generalFlatBand_siteAnnihilation_eq_zero`.)  This is the trivial branch of eq. (11.3.48): a site
disconnected from the basis contributes no sign relation. -/
theorem flatBandSpinConfigState_cDownUp_eq_zero_of_disconnected
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    {x : Fin (M + 1)} (hx : ∀ z ∈ I, μ z x = 0) :
    (generalCDownUp M x).mulVec (flatBandSpinConfigState I idx eμ σ) = 0 := by
  rw [flatBandSpinConfigState_cDownUp_eq_slaterDoubleAnnih hidx,
    generalFlatBand_siteAnnihilation_eq_zero μ x 0 _ (fun q hq => Or.inl ?_), Matrix.mulVec_zero]
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
  have hgw : flatBandSpinConfigOcc I idx σ w = 1 := by
    have := Finset.mem_toList.mp hw
    simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
  exact hx _ (flatBandSpecialIdxInv_mem
    (Finset.mem_image.mp (flatBandSpinConfigOcc_idxSupported I idx σ w hgw)))

end LatticeSystem.Fermion

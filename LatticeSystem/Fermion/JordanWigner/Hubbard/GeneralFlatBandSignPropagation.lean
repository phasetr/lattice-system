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

/-- **Tasaki eq. (11.3.47) as an explicit `C(σ)` sum**: a flat-band Hubbard ground state is an
explicit finite linear combination `Φ = Σ_σ C(σ)·flatBandSpinConfigState σ` of the
spin-configuration states, over all spin configurations `σ : Fin (M+1) → Fin 2`.  The coefficients
`C(σ)` (well-defined
up to the redundancy off `I`, pinned down by the linear independence `PR12`) are the `C(σ)` of
eqs. (11.3.47)–(11.3.48).  From `flatBand_groundState_mem_spinConfigStateSpan` (PR11) and
`Submodule.mem_span_range_iff_exists_fun`. -/
theorem flatBand_groundState_eq_spinConfigStateSum
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    ∃ C : (Fin (M + 1) → Fin 2) → ℂ,
      Φ = ∑ σ, C σ • flatBandSpinConfigState I idx eμ σ := by
  obtain ⟨C, hC⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (flatBand_groundState_mem_spinConfigStateSpan hbasis hT U hU eμ idx hidx hΦ)
  exact ⟨C, hC.symm⟩

end LatticeSystem.Fermion

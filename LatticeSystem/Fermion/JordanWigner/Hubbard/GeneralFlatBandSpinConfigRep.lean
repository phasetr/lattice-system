import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandSpinConfigRepCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralBasisHN

/-!
# Spin-configuration capstone, eq. (11.3.47) (Tasaki §11.3.4, toward Theorem 11.17)

PR8 (`flatBand_groundState_mem_imode`) places a flat-band Hubbard ground state `Φ` (at filling
`D₀`) in the tight `I`-mode `μ`-Slater Fock submodule.  Tasaki's eq. (11.3.47) refines this to the
*spin-configuration* form

`Φ = Σ_{σ : I → {↑,↓}} C(σ)·Π_{z∈I} â†_{μ_z,σ_z}|vac⟩`,

i.e. every index `z ∈ I` is occupied by **exactly one** spin.

The argument works in the general occupation basis `generalOccBasis eμ` over the extended
single-particle basis `eμ` (PR8 `exists_extended_special_basis`, `eμ (idx z) = μ_z`).  The flat-band
ground state's occupation-basis coefficients vanish off the spin configurations:

* **support** — `repr Φ g = 0` unless `g` is supported on the index modes `idx(I)`;
* **filling** — `repr Φ g = 0` unless `|occupied g| = D₀`;
* **no double occupancy** — `repr Φ g = 0` if some index mode `idx z` is doubly occupied.

This module records the support and filling coefficient-vanishing facts first.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.47).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators ComplexOrder

variable {M : ℕ}

/-- **Tasaki eq. (11.3.47) (spin-configuration representation)**: a flat-band Hubbard ground state
`Φ` (Hermitian PSD hopping `T`, `U > 0`, filling `D₀`) lies in the span of the occupation monomials
of the **spin configurations** — the `idx(I)`-supported configs with **no doubly occupied index
mode** and exactly `D₀` occupied modes.  Since `D₀ = |I|`, such a config occupies each index mode
`idx z` (`z ∈ I`) by exactly one spin, i.e. it is a one-spin-per-index `μ`-Slater state
`Π_{z∈I} â†_{μ_z,σ_z}|vac⟩`.

Assembled from the three coefficient-vanishing facts: support
(`flatBand_groundState_eμ_repr_eq_zero_of_not_idxSupported`), no double occupancy
(`flatBand_groundState_eμ_repr_eq_zero_of_doublyOccupied`), and filling
(`generalOccBasis_repr_eq_zero_of_card_ne`). -/
theorem flatBand_groundState_mem_spinConfigSpan
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    Φ ∈ Submodule.span ℂ
      {v | ∃ g, IsIdxSupported I idx g
        ∧ (∀ z ∈ I, ¬ (g (idx z, 0) = 1 ∧ g (idx z, 1) = 1))
        ∧ (generalOccFinset g).card = generalFlatBandDim T
        ∧ generalOccMonomial eμ g = v} := by
  classical
  set b := generalOccBasis eμ with hb
  have hbcoe : ∀ h, (b h : (Fin (2 * M + 2) → Fin 2) → ℂ) = generalOccMonomial eμ h :=
    fun h => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) h
  have hN : (fermionTotalNumber (2 * M + 1)).mulVec Φ = (generalFlatBandDim T : ℂ) • Φ := by
    have h := (Submodule.mem_inf.mp hΦ).2
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h
    exact h
  rw [← b.sum_repr Φ]
  refine Submodule.sum_mem _ fun g _ => ?_
  by_cases hsupp : IsIdxSupported I idx g
  · by_cases hdbl : ∃ z ∈ I, g (idx z, 0) = 1 ∧ g (idx z, 1) = 1
    · obtain ⟨z, hz, h0, h1⟩ := hdbl
      rw [flatBand_groundState_eμ_repr_eq_zero_of_doublyOccupied hbasis hT U hU eμ idx hidx hΦ
        g hz h0 h1, zero_smul]
      exact Submodule.zero_mem _
    · by_cases hcard : (generalOccFinset g).card = generalFlatBandDim T
      · refine Submodule.smul_mem _ _ (Submodule.subset_span
          ⟨g, hsupp, fun z hz hc => hdbl ⟨z, hz, hc⟩, hcard, (hbcoe g).symm⟩)
      · rw [generalOccBasis_repr_eq_zero_of_card_ne eμ hN g hcard, zero_smul]
        exact Submodule.zero_mem _
  · rw [flatBand_groundState_eμ_repr_eq_zero_of_not_idxSupported hbasis hT U hU eμ idx hidx hΦ
      g hsupp, zero_smul]
    exact Submodule.zero_mem _

/-- Two distinct `Fin 2` values are `0` and `1` in some order. -/
theorem fin2_ne_cases {a b : Fin 2} (h : a ≠ b) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  fin_cases a <;> fin_cases b <;> simp_all

/-- Every `Fin 2` value is `0` or `1`. -/
theorem fin2_eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- **One spin per index (the pigeonhole behind eq. (11.3.47))**: a spin-configuration occupation
`g` (`idx(I)`-supported, no doubly occupied index mode, exactly `D₀` occupied) occupies **every**
index mode `idx z` (`z ∈ I`) by at least one spin.  Since `D₀ = |I|` and the first-coordinate
projection is injective on the occupied finset (no double occupancy), it surjects onto `idx(I)`. -/
theorem flatBandSpinConfig_occupied_per_index
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) {g : Fin (M + 1) × Fin 2 → Fin 2}
    (hsupp : IsIdxSupported I idx g)
    (hno : ∀ z ∈ I, ¬ (g (idx z, 0) = 1 ∧ g (idx z, 1) = 1))
    (hcard : (generalOccFinset g).card = generalFlatBandDim T) {z : Fin (M + 1)} (hz : z ∈ I) :
    g (idx z, 0) = 1 ∨ g (idx z, 1) = 1 := by
  classical
  have hgmem : ∀ {q : Fin (M + 1) × Fin 2}, q ∈ generalOccFinset g → g q = 1 := fun {q} hq => by
    simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hq
  have hinjOn : Set.InjOn (Prod.fst : Fin (M + 1) × Fin 2 → Fin (M + 1)) ↑(generalOccFinset g) := by
    intro q hq q' hq' hqq
    rw [Finset.mem_coe] at hq hq'
    by_contra hne
    have h2 : q.2 ≠ q'.2 := fun h => hne (Prod.ext hqq h)
    obtain ⟨w, hw, hwq⟩ := Finset.mem_image.mp (hsupp q (hgmem hq))
    have hqw : q = (idx w, q.2) := Prod.ext hwq.symm rfl
    have hq'w : q' = (idx w, q'.2) := Prod.ext (by rw [← hqq, ← hwq]) rfl
    have hga : g (idx w, q.2) = 1 := hqw ▸ hgmem hq
    have hgb : g (idx w, q'.2) = 1 := hq'w ▸ hgmem hq'
    refine hno w hw ?_
    rcases fin2_ne_cases h2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨ha ▸ hga, hb ▸ hgb⟩
    · exact ⟨hb ▸ hgb, ha ▸ hga⟩
  -- the projection image of the occupied finset is all of `idx(I)`
  set π : Fin (M + 1) × Fin 2 → Fin (M + 1) := Prod.fst with hπ
  have hsub : (generalOccFinset g).image π ⊆ I.image idx := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hsupp q (hgmem hq)
  have hidxinj : Set.InjOn idx ↑I := fun a ha b hb hab =>
    flatBandSpecial_idx_injOn hbasis hidx (Finset.mem_coe.mp ha) (Finset.mem_coe.mp hb) hab
  have hcardeq : ((generalOccFinset g).image π).card = (I.image idx).card := by
    rw [Finset.card_image_of_injOn hinjOn, Finset.card_image_of_injOn hidxinj, hcard]
    exact (hbasis.1).symm
  have himg : (generalOccFinset g).image π = I.image idx :=
    Finset.eq_of_subset_of_card_le hsub hcardeq.ge
  have hmem : idx z ∈ (generalOccFinset g).image π := by
    rw [himg]; exact Finset.mem_image_of_mem idx hz
  obtain ⟨q, hq, hqfst⟩ := Finset.mem_image.mp hmem
  have hgq : g q = 1 := hgmem hq
  have hqeq : q = (idx z, q.2) := Prod.ext hqfst rfl
  rw [hqeq] at hgq
  rcases fin2_eq_zero_or_one q.2 with h | h
  · left; rw [h] at hgq; exact hgq
  · right; rw [h] at hgq; exact hgq

/-- **Exactly one spin per index, eq. (11.3.47) explicit form**: a spin-configuration occupation `g`
(`idx(I)`-supported, no double occupancy, `D₀` occupied) occupies every index mode `idx z` (`z ∈ I`)
by **exactly one** spin.  Combines the pigeonhole `flatBandSpinConfig_occupied_per_index` (at least
one) with the no-double-occupancy hypothesis (not both). -/
theorem flatBandSpinConfig_exactlyOne_per_index
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) {g : Fin (M + 1) × Fin 2 → Fin 2}
    (hsupp : IsIdxSupported I idx g)
    (hno : ∀ z ∈ I, ¬ (g (idx z, 0) = 1 ∧ g (idx z, 1) = 1))
    (hcard : (generalOccFinset g).card = generalFlatBandDim T) {z : Fin (M + 1)} (hz : z ∈ I) :
    (g (idx z, 0) = 1 ∧ g (idx z, 1) ≠ 1) ∨ (g (idx z, 0) ≠ 1 ∧ g (idx z, 1) = 1) := by
  rcases flatBandSpinConfig_occupied_per_index hbasis hidx hsupp hno hcard hz with h0 | h1
  · exact Or.inl ⟨h0, fun h1 => hno z hz ⟨h0, h1⟩⟩
  · exact Or.inr ⟨fun h0 => hno z hz ⟨h0, h1⟩, h1⟩

/-- **The one-spin-per-index occupation of a spin configuration** `σ : Fin (M+1) → Fin 2`: the
config occupying exactly the modes `(idx z, σ z)` for `z ∈ I`.  Its occupation monomial is the
spin-configuration `μ`-Slater state `Π_{z∈I} â†_{μ_z,σ_z}|vac⟩` of eq. (11.3.47). -/
noncomputable def flatBandSpinConfigOcc (I : Finset (Fin (M + 1)))
    (idx : Fin (M + 1) → Fin (M + 1)) (σ : Fin (M + 1) → Fin 2) :
    Fin (M + 1) × Fin 2 → Fin 2 :=
  fun q => if ∃ z ∈ I, q = (idx z, σ z) then 1 else 0

open Classical in
/-- **The spin-configuration state** `Π_{z∈I} â†_{μ_z,σ_z}|vac⟩`, indexed by a spin configuration
`σ` (the summands of eq. (11.3.47)), realised as the occupation monomial of `flatBandSpinConfigOcc`
over the extended basis `eμ`. -/
noncomputable def flatBandSpinConfigState (I : Finset (Fin (M + 1)))
    (idx : Fin (M + 1) → Fin (M + 1))
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (σ : Fin (M + 1) → Fin 2) :
    (Fin (2 * M + 2) → Fin 2) → ℂ :=
  generalOccMonomial eμ (flatBandSpinConfigOcc I idx σ)

/-- **A spin-configuration occupation `g` is `flatBandSpinConfigOcc` of its spin function**: with
`σ_g z := [g(idx z,↑) ≠ 1]`, a spin-config occupation (`idx(I)`-supported, no double occupancy, `D₀`
occupied) equals `flatBandSpinConfigOcc I idx σ_g`.  Uses the explicit one-spin-per-index property
(`flatBandSpinConfig_exactlyOne_per_index`). -/
theorem flatBandSpinConfig_eq_spinConfigOcc
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) {g : Fin (M + 1) × Fin 2 → Fin 2}
    (hsupp : IsIdxSupported I idx g)
    (hno : ∀ z ∈ I, ¬ (g (idx z, 0) = 1 ∧ g (idx z, 1) = 1))
    (hcard : (generalOccFinset g).card = generalFlatBandDim T) :
    g = flatBandSpinConfigOcc I idx (fun z => if g (idx z, 0) = 1 then 0 else 1) := by
  classical
  have hinj : ∀ {a b : Fin (M + 1)}, a ∈ I → b ∈ I → idx a = idx b → a = b :=
    fun {a b} ha hb => flatBandSpecial_idx_injOn hbasis hidx ha hb
  funext q
  set σg : Fin (M + 1) → Fin 2 := fun z => if g (idx z, 0) = 1 then 0 else 1 with hσg
  by_cases hq : q.1 ∈ I.image idx
  · obtain ⟨z, hz, hzq⟩ := Finset.mem_image.mp hq
    have hqz : q = (idx z, q.2) := Prod.ext hzq.symm rfl
    -- value of the spin-config occupation at q
    have hocc : flatBandSpinConfigOcc I idx σg q = if q.2 = σg z then 1 else 0 := by
      unfold flatBandSpinConfigOcc
      by_cases hτ : q.2 = σg z
      · rw [if_pos ⟨z, hz, by rw [hqz, hτ]⟩, if_pos hτ]
      · rw [if_neg hτ, if_neg ?_]
        rintro ⟨w, hw, hwq⟩
        have e1 : q.1 = idx w := by rw [hwq]
        rw [← hzq] at e1
        have hwz : idx w = idx z := e1.symm
        exact hτ (by rw [hwq, hinj hw hz hwz])
    rw [hocc]
    conv_lhs => rw [hqz]
    rcases flatBandSpinConfig_exactlyOne_per_index hbasis hidx hsupp hno hcard hz with
      ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have hσz : σg z = 0 := by rw [hσg]; exact if_pos h0
      have hg1 : g (idx z, 1) = 0 := (fin2_eq_zero_or_one _).resolve_right h1
      rcases fin2_eq_zero_or_one q.2 with h | h <;> rw [h, hσz]
      · rw [if_pos rfl]; exact h0
      · rw [if_neg (by decide)]; exact hg1
    · have hσz : σg z = 1 := by rw [hσg]; exact if_neg h0
      have hg0 : g (idx z, 0) = 0 := (fin2_eq_zero_or_one _).resolve_right h0
      rcases fin2_eq_zero_or_one q.2 with h | h <;> rw [h, hσz]
      · rw [if_neg (by decide)]; exact hg0
      · rw [if_pos rfl]; exact h1
  · have hg0 : g q = 0 := (fin2_eq_zero_or_one (g q)).resolve_right (fun h => hq (hsupp q h))
    rw [hg0]
    unfold flatBandSpinConfigOcc
    rw [if_neg ?_]
    rintro ⟨w, hw, hwq⟩
    exact hq (by rw [hwq]; exact Finset.mem_image_of_mem idx hw)

/-- **Tasaki eq. (11.3.47), `σ`-parametrised form**: a flat-band Hubbard ground state lies in the
span of the spin-configuration states `flatBandSpinConfigState` ranging over all spin configurations
`σ : Fin (M+1) → Fin 2`.  From `flatBand_groundState_mem_spinConfigSpan` (PR9), each surviving
spin-config occupation equals `flatBandSpinConfigOcc` of its spin function (PR10
one-spin-per-index), so its occupation monomial is a `flatBandSpinConfigState`. -/
theorem flatBand_groundState_mem_spinConfigStateSpan
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    Φ ∈ Submodule.span ℂ (Set.range (flatBandSpinConfigState I idx eμ)) := by
  refine (Submodule.span_le.mpr ?_)
    (flatBand_groundState_mem_spinConfigSpan hbasis hT U hU eμ idx hidx hΦ)
  rintro _ ⟨g, hsupp, hno, hcard, rfl⟩
  refine Submodule.subset_span ⟨fun z => if g (idx z, 0) = 1 then 0 else 1, ?_⟩
  rw [flatBandSpinConfigState, ← flatBandSpinConfig_eq_spinConfigOcc hbasis hidx hsupp hno hcard]

end LatticeSystem.Fermion

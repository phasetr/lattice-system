import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandSpinRep
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralBasisHN

/-!
# General flat-band ground states: index-supported representation (foundation)

Foundational layer extracted from `GeneralFlatBandSpinConfigRep.lean` for build speed
(Tasaki §11.3.4, eq. (11.3.47)).  This file develops the index-supported predicate
`IsIdxSupported`, the special-index inverse / preimage-list machinery, the
coefficient-vanishing facts (support / double-occupancy / filling), and the
occupation-monomial bridge that feed the spin-configuration representation theorems
`flatBand_groundState_mem_spinConfigSpan`, `flatBandSpinConfig_eq_spinConfigOcc` and
`flatBand_groundState_mem_spinConfigStateSpan` kept in the capstone module
`GeneralFlatBandSpinConfigRep.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §11.3.4, eq. (11.3.47).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators ComplexOrder

variable {M : ℕ}


/-- An occupation config `g` is **`idx(I)`-supported** when every occupied mode lies over an index
mode `idx z` (`z ∈ I`): `g q = 1 → q.1 ∈ idx(I)`.  These are the configs whose occupation monomial
is an `I`-mode `μ`-Slater state. -/
def IsIdxSupported (I : Finset (Fin (M + 1))) (idx : Fin (M + 1) → Fin (M + 1))
    (g : Fin (M + 1) × Fin 2 → Fin 2) : Prop :=
  ∀ q : Fin (M + 1) × Fin 2, g q = 1 → q.1 ∈ I.image idx

/-- **A mode monomial with all modes in `idx(I)` lies in the span of the `idx(I)`-supported
occupation monomials.**  (The `idx(I)`-restricted analogue of
`generalModeMonomial_mem_span_occMonomial`: reorder to the occupied-finset list of the indicator
config, which is `idx(I)`-supported.) -/
theorem generalModeMonomial_mem_span_idxSupported
    {I : Finset (Fin (M + 1))} (idx : Fin (M + 1) → Fin (M + 1))
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (l : List (Fin (M + 1) × Fin 2))
    (hl : ∀ q ∈ l, q.1 ∈ I.image idx) :
    generalModeMonomial eμ l ∈ Submodule.span ℂ
      {v | ∃ h, IsIdxSupported I idx h ∧ generalOccMonomial eμ h = v} := by
  classical
  by_cases hnd : l.Nodup
  · set f : Fin (M + 1) × Fin 2 → Fin 2 := fun q => if q ∈ l.toFinset then 1 else 0 with hf
    have hocc : generalOccFinset f = l.toFinset := by
      ext q
      simp only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and, hf]
      by_cases h : q ∈ l.toFinset <;> simp [h]
    have hfsupp : IsIdxSupported I idx f := by
      intro q hq
      have hmem : q ∈ l.toFinset := by
        by_contra hc
        have hfq : f q = 0 := by rw [hf]; exact if_neg hc
        rw [hfq] at hq
        exact absurd hq (by decide)
      exact hl q (List.mem_toFinset.mp hmem)
    have hperm : l.Perm (generalOccFinset f).toList := by
      rw [hocc]; exact (List.toFinset_toList hnd).symm
    obtain ⟨z, _, hz⟩ := generalModeMonomial_perm eμ hperm
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, hfsupp, rfl⟩)
  · rw [generalModeMonomial_eq_zero_of_not_nodup eμ l hnd]
    exact Submodule.zero_mem _

/-- **A flat-band ground state lies in the span of the `idx(I)`-supported occupation monomials.**
From PR8 (`flatBand_groundState_mem_imode`, the `I`-mode `μ`-Slater submodule) carried through the
`μ`-Slater↔mode-monomial bridge (`generalFlatBandSlaterState_eq_generalModeMonomial`). -/
theorem flatBand_groundState_mem_span_idxSupported
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    Φ ∈ Submodule.span ℂ
      {v | ∃ h, IsIdxSupported I idx h ∧ generalOccMonomial eμ h = v} := by
  have hmem := flatBand_groundState_mem_imode hbasis hT U hU hΦ
  refine (Submodule.span_le.mpr ?_) hmem
  rintro _ ⟨qs, hqs, rfl⟩
  rw [generalFlatBandSlaterState_eq_generalModeMonomial eμ idx hidx qs hqs]
  refine generalModeMonomial_mem_span_idxSupported idx eμ _ fun q hq => ?_
  simp only [List.mem_map] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  exact Finset.mem_image_of_mem idx (hqs q' hq')

/-- **Support coefficient vanishing**: a flat-band ground state's `eμ`-occupation-basis coefficient
vanishes on every config that is *not* `idx(I)`-supported.  From the span membership and
`Basis.repr_support_subset_of_mem_span`. -/
theorem flatBand_groundState_eμ_repr_eq_zero_of_not_idxSupported
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (g : Fin (M + 1) × Fin 2 → Fin 2) (hg : ¬ IsIdxSupported I idx g) :
    (generalOccBasis eμ).repr Φ g = 0 := by
  set b := generalOccBasis eμ with hb
  have hbcoe : ∀ h, (b h : (Fin (2 * M + 2) → Fin 2) → ℂ) = generalOccMonomial eμ h :=
    fun h => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) h
  have hset : (b '' {h | IsIdxSupported I idx h})
      = {v | ∃ h, IsIdxSupported I idx h ∧ generalOccMonomial eμ h = v} := by
    ext v
    constructor
    · rintro ⟨h, hh, rfl⟩; exact ⟨h, hh, (hbcoe h).symm⟩
    · rintro ⟨h, hh, rfl⟩; exact ⟨h, hh, hbcoe h⟩
  have hmem : Φ ∈ Submodule.span ℂ (b '' {h | IsIdxSupported I idx h}) := by
    rw [hset]
    exact flatBand_groundState_mem_span_idxSupported hbasis hT U hU eμ idx hidx hΦ
  have hsub := b.repr_support_subset_of_mem_span {h | IsIdxSupported I idx h} hmem
  by_contra hne
  exact hg (hsub (Finsupp.mem_support_iff.mpr hne))

/-- The index map `idx` (sending `z ∈ I` to the `eμ`-index of `μ_z`) is **injective on `I`**:
distinct indices give distinct `μ`-vectors (special-basis linear independence), hence distinct
`eμ`-indices. -/
theorem flatBandSpecial_idx_injOn {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {a : Fin (M + 1)} (ha : a ∈ I) {b : Fin (M + 1)} (hb : b ∈ I) (hab : idx a = idx b) :
    a = b := by
  obtain ⟨_, _, hli, _, _⟩ := hbasis
  have hμ : (fun z : I => (μ z.1 : Fin (M + 1) → ℂ)) ⟨a, ha⟩
      = (fun z : I => (μ z.1 : Fin (M + 1) → ℂ)) ⟨b, hb⟩ := by
    simp only [← hidx a ha, ← hidx b hb, hab]
  exact Subtype.ext_iff.mp (hli.injective hμ)

open Classical in
/-- A **left inverse of `idx` on `I`**: for `y` in the image `idx(I)`, it returns a preimage in `I`
(`idx ∘ idxInv = id` on `idx(I)`); elsewhere it is irrelevant. -/
noncomputable def flatBandSpecialIdxInv (I : Finset (Fin (M + 1)))
    (idx : Fin (M + 1) → Fin (M + 1)) (y : Fin (M + 1)) : Fin (M + 1) :=
  if h : ∃ w ∈ I, idx w = y then h.choose else default

/-- `idx (idxInv y) = y` whenever `y ∈ idx(I)`. -/
theorem idx_flatBandSpecialIdxInv {I : Finset (Fin (M + 1))} {idx : Fin (M + 1) → Fin (M + 1)}
    {y : Fin (M + 1)} (h : ∃ w ∈ I, idx w = y) :
    idx (flatBandSpecialIdxInv I idx y) = y := by
  rw [flatBandSpecialIdxInv, dif_pos h]; exact h.choose_spec.2

/-- `idxInv y ∈ I` whenever `y ∈ idx(I)`. -/
theorem flatBandSpecialIdxInv_mem {I : Finset (Fin (M + 1))} {idx : Fin (M + 1) → Fin (M + 1)}
    {y : Fin (M + 1)} (h : ∃ w ∈ I, idx w = y) :
    flatBandSpecialIdxInv I idx y ∈ I := by
  rw [flatBandSpecialIdxInv, dif_pos h]; exact h.choose_spec.1

/-- `idxInv (idx w) = w` for `w ∈ I` (genuine left inverse on `I`, using injectivity). -/
theorem flatBandSpecialIdxInv_idx {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) {w : Fin (M + 1)} (hw : w ∈ I) :
    flatBandSpecialIdxInv I idx (idx w) = w := by
  have hex : ∃ v ∈ I, idx v = idx w := ⟨w, hw, rfl⟩
  exact flatBandSpecial_idx_injOn hbasis hidx (flatBandSpecialIdxInv_mem hex) hw
    (idx_flatBandSpecialIdxInv hex)

/-- The **`μ`-Slater preimage list** of an `idx(I)`-supported config `g`: the occupied modes of `g`
pulled back along `idxInv` to the index set `I`.  Its `μ`-Slater state is `occMon_eμ g`. -/
noncomputable def flatBandSpecialPreimageList (I : Finset (Fin (M + 1)))
    (idx : Fin (M + 1) → Fin (M + 1)) (g : Fin (M + 1) × Fin 2 → Fin 2) :
    List (Fin (M + 1) × Fin 2) :=
  ((generalOccFinset g).toList).map (fun q => (flatBandSpecialIdxInv I idx q.1, q.2))

/-- Every mode of the preimage list lies over `I` (for an `idx(I)`-supported `g`). -/
theorem flatBandSpecialPreimageList_mem {I : Finset (Fin (M + 1))}
    {idx : Fin (M + 1) → Fin (M + 1)} {g : Fin (M + 1) × Fin 2 → Fin 2}
    (hg : IsIdxSupported I idx g) (q : Fin (M + 1) × Fin 2)
    (hq : q ∈ flatBandSpecialPreimageList I idx g) : q.1 ∈ I := by
  rw [flatBandSpecialPreimageList, List.mem_map] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  have hgq : g q' = 1 := by
    have := Finset.mem_toList.mp hq'
    simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
  exact flatBandSpecialIdxInv_mem (Finset.mem_image.mp (hg q' hgq))

/-- Mapping the preimage list back through `idx` recovers the occupied-mode list of `g`. -/
theorem flatBandSpecialPreimageList_map_idx {I : Finset (Fin (M + 1))}
    {idx : Fin (M + 1) → Fin (M + 1)} {g : Fin (M + 1) × Fin 2 → Fin 2}
    (hg : IsIdxSupported I idx g) :
    (flatBandSpecialPreimageList I idx g).map (fun q => (idx q.1, q.2))
      = (generalOccFinset g).toList := by
  rw [flatBandSpecialPreimageList, List.map_map]
  refine (List.map_congr_left ?_).trans (List.map_id _)
  intro q hq
  have hgq : g q = 1 := by
    have := Finset.mem_toList.mp hq
    simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
  simp only [Function.comp_apply, idx_flatBandSpecialIdxInv (Finset.mem_image.mp (hg q hgq)),
    Prod.mk.eta, id_eq]

/-- **`occMon_eμ g` is an `I`-mode `μ`-Slater state** (for an `idx(I)`-supported `g`), namely the
state of its `μ`-Slater preimage list.  Via the forward bridge
`generalFlatBandSlaterState_eq_generalModeMonomial`. -/
theorem generalOccMonomial_eq_generalFlatBandSlaterState_of_idxSupported
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) {g : Fin (M + 1) × Fin 2 → Fin 2}
    (hg : IsIdxSupported I idx g) :
    generalOccMonomial eμ g
      = generalFlatBandSlaterState μ (flatBandSpecialPreimageList I idx g) := by
  rw [generalFlatBandSlaterState_eq_generalModeMonomial eμ idx hidx _
        (flatBandSpecialPreimageList_mem hg),
    flatBandSpecialPreimageList_map_idx hg, generalOccMonomial]

/-- **The occupation count of the preimage list** equals `g` at the index mode: for `z ∈ I`,
`count (z,σ) (preimage list) = [g(idx z,σ) = 1]`.  (The list is `idx(I)`-injective, hence nodup, and
`(z,σ)` occurs iff `idx z` is occupied with spin `σ`.) -/
theorem flatBandSpecialPreimageList_count
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) {g : Fin (M + 1) × Fin 2 → Fin 2}
    (hg : IsIdxSupported I idx g) {z : Fin (M + 1)} (hz : z ∈ I) (σ : Fin 2) :
    ((flatBandSpecialPreimageList I idx g).count (z, σ) : ℂ)
      = if g (idx z, σ) = 1 then 1 else 0 := by
  classical
  set ps := flatBandSpecialPreimageList I idx g with hps
  have hnd : ps.Nodup := by
    rw [hps, flatBandSpecialPreimageList]
    refine ((generalOccFinset g).nodup_toList).map_on ?_
    intro a ha b hb hfab
    have hga : g a = 1 := by
      have := Finset.mem_toList.mp ha
      simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have hgb : g b = 1 := by
      have := Finset.mem_toList.mp hb
      simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have h1 : flatBandSpecialIdxInv I idx a.1 = flatBandSpecialIdxInv I idx b.1 :=
      (Prod.ext_iff.mp hfab).1
    have ha1 : idx (flatBandSpecialIdxInv I idx a.1) = a.1 :=
      idx_flatBandSpecialIdxInv (Finset.mem_image.mp (hg a hga))
    have hb1 : idx (flatBandSpecialIdxInv I idx b.1) = b.1 :=
      idx_flatBandSpecialIdxInv (Finset.mem_image.mp (hg b hgb))
    exact Prod.ext (by rw [← ha1, h1, hb1]) (Prod.ext_iff.mp hfab).2
  have hiff : (z, σ) ∈ ps ↔ g (idx z, σ) = 1 := by
    rw [hps, flatBandSpecialPreimageList, List.mem_map]
    constructor
    · rintro ⟨q, hq, hfq⟩
      have hgq : g q = 1 := by
        have := Finset.mem_toList.mp hq
        simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
      have hq1 : idx (flatBandSpecialIdxInv I idx q.1) = q.1 :=
        idx_flatBandSpecialIdxInv (Finset.mem_image.mp (hg q hgq))
      have hzeq : flatBandSpecialIdxInv I idx q.1 = z := (Prod.ext_iff.mp hfq).1
      have hσeq : q.2 = σ := (Prod.ext_iff.mp hfq).2
      have hqeq : (idx z, σ) = q := by
        rw [hzeq] at hq1; exact Prod.ext hq1 hσeq.symm
      rw [hqeq]; exact hgq
    · intro hgz
      refine ⟨(idx z, σ), ?_, ?_⟩
      · rw [Finset.mem_toList]
        simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hgz
      · exact Prod.ext (flatBandSpecialIdxInv_idx hbasis hidx hz) rfl
  by_cases hmem : (z, σ) ∈ ps
  · rw [List.count_eq_one_of_mem hnd hmem, Nat.cast_one, if_pos (hiff.mp hmem)]
  · rw [List.count_eq_zero_of_not_mem hmem, Nat.cast_zero, if_neg (fun hc => hmem (hiff.mpr hc))]

/-- **The double index-mode number operator is diagonal on `idx(I)`-supported occupation
monomials**,
with eigenvalue `μ_z(z)²·[g(idx z,↑)=1]·[g(idx z,↓)=1]`.  Combines the two single diagonal actions
(`muNumberOp_mulVec_generalFlatBandSlaterState`) through the `occMon_eμ ↔ μ`-Slater bridge. -/
theorem muNumberOp_double_mulVec_generalOccMonomial_of_idxSupported
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) {g : Fin (M + 1) × Fin 2 → Fin 2}
    (hg : IsIdxSupported I idx g) {z : Fin (M + 1)} (hz : z ∈ I) :
    (muNumberOp μ z 0 * muNumberOp μ z 1).mulVec (generalOccMonomial eμ g)
      = ((μ z z * (if g (idx z, 0) = 1 then (1 : ℂ) else 0))
          * (μ z z * (if g (idx z, 1) = 1 then (1 : ℂ) else 0)))
        • generalOccMonomial eμ g := by
  have hbridge := generalOccMonomial_eq_generalFlatBandSlaterState_of_idxSupported hidx hg
  rw [hbridge, ← Matrix.mulVec_mulVec,
    muNumberOp_mulVec_generalFlatBandSlaterState hbasis hz 1 _
      (flatBandSpecialPreimageList_mem hg),
    Matrix.mulVec_smul,
    muNumberOp_mulVec_generalFlatBandSlaterState hbasis hz 0 _
      (flatBandSpecialPreimageList_mem hg),
    smul_smul, flatBandSpecialPreimageList_count hbasis hidx hg hz 1,
    flatBandSpecialPreimageList_count hbasis hidx hg hz 0, ← hbridge]
  congr 1
  ring

/-- **No-double-occupancy coefficient vanishing**: a flat-band ground state's `eμ`-occupation-basis
coefficient vanishes on every config with a *doubly occupied* index mode
(`g(idx z,↑) = g(idx z,↓) = 1` for some `z ∈ I`).  From
`muNumberOp_double_mulVec_eq_zero_of_mem_groundSubmodule` (PR7) and the diagonal action: expanding
`Φ` in the basis, the double number operator has eigenvalue `μ_z(z)² ≠ 0` on such configs and `0`
on the others, so `μ_z(z)²·c_g = 0`. -/
theorem flatBand_groundState_eμ_repr_eq_zero_of_doublyOccupied
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (g : Fin (M + 1) × Fin 2 → Fin 2) {z : Fin (M + 1)} (hz : z ∈ I)
    (h0 : g (idx z, 0) = 1) (h1 : g (idx z, 1) = 1) :
    (generalOccBasis eμ).repr Φ g = 0 := by
  classical
  set b := generalOccBasis eμ with hb
  have hbcoe : ∀ h, (b h : (Fin (2 * M + 2) → Fin 2) → ℂ) = generalOccMonomial eμ h :=
    fun h => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) h
  have hzero := muNumberOp_double_mulVec_eq_zero_of_mem_groundSubmodule hbasis hT U hU hz hΦ
  have hexp : (muNumberOp μ z 0 * muNumberOp μ z 1).mulVec Φ
      = ∑ h, (b.repr Φ h
          * ((μ z z * (if h (idx z, 0) = 1 then (1 : ℂ) else 0))
              * (μ z z * (if h (idx z, 1) = 1 then (1 : ℂ) else 0)))) • (b h) := by
    conv_lhs => rw [← b.sum_repr Φ]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Matrix.mulVec_smul]
    by_cases hsupp : IsIdxSupported I idx h
    · rw [hbcoe, muNumberOp_double_mulVec_generalOccMonomial_of_idxSupported hbasis hidx hsupp hz,
        ← hbcoe, smul_smul]
    · rw [flatBand_groundState_eμ_repr_eq_zero_of_not_idxSupported hbasis hT U hU eμ idx hidx hΦ
        h hsupp, zero_smul, zero_mul, zero_smul]
  have hrepr : b.repr ((muNumberOp μ z 0 * muNumberOp μ z 1).mulVec Φ) g
      = b.repr Φ g
        * ((μ z z * (if g (idx z, 0) = 1 then (1 : ℂ) else 0))
            * (μ z z * (if g (idx z, 1) = 1 then (1 : ℂ) else 0))) := by
    rw [hexp, map_sum]
    simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, b.repr_self]
    rw [Finset.sum_eq_single g]
    · rw [Finsupp.single_eq_same, mul_one]
    · intro h _ hhg
      rw [Finsupp.single_eq_of_ne (Ne.symm hhg), mul_zero]
    · intro h; exact absurd (Finset.mem_univ g) h
  rw [hzero, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hrepr
  have hev : (μ z z * (if g (idx z, 0) = 1 then (1 : ℂ) else 0))
      * (μ z z * (if g (idx z, 1) = 1 then (1 : ℂ) else 0)) = μ z z * μ z z := by
    rw [if_pos h0, if_pos h1]; ring
  rw [hev] at hrepr
  obtain ⟨_, _, _, hμz, _⟩ := hbasis
  have hne : μ z z * μ z z ≠ 0 := mul_ne_zero (hμz z hz) (hμz z hz)
  exact (mul_eq_zero.mp hrepr.symm).resolve_right hne

end LatticeSystem.Fermion

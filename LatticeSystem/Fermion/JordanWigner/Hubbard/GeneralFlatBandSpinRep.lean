import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandSpinConfig

/-!
# Spin representation capstone (Tasaki §11.3.4, eq. 11.3.47, Theorem 11.17)

The no-double-occupancy of the index modes (PR7) plus the filling constraint (PR5) pin a flat-band
ground state to the *one-spin-per-index* `μ`-Slater states.  To extract the occupation coefficients
we use a `μ`-occupation basis: the special basis `{μ_z}_{z∈I}` is linearly independent, so it
extends
to a basis of the whole single-particle space `Fin (M+1) → ℂ`, on which the general occupation basis
(`generalOccBasis`, PR2) is built.

This module begins with that basis extension.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.47).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped ComplexOrder

variable {M : ℕ}

/-- **The special basis extends to a full single-particle basis**: since `{μ_z}_{z∈I}` is linearly
independent in `Fin (M+1) → ℂ`, it extends to a basis `eμ` of the whole space, each `μ_z` appearing
as some `eμ i`.  (Reindexed to `Fin (M+1)` for compatibility with `generalOccBasis`.) -/
theorem exists_extended_special_basis
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ) :
    ∃ eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ),
      ∀ z ∈ I, ∃ i, (eμ i : Fin (M + 1) → ℂ) = μ z := by
  classical
  obtain ⟨_, _, hli, _, _⟩ := hbasis
  have hinj : Function.Injective (fun z : I => (μ z.1 : Fin (M + 1) → ℂ)) := hli.injective
  have hli' : LinearIndepOn ℂ (id : (Fin (M + 1) → ℂ) → Fin (M + 1) → ℂ)
      (Set.range (fun z : I => (μ z.1 : Fin (M + 1) → ℂ))) :=
    (linearIndepOn_id_range_iff hinj).mpr hli
  set b := Basis.extend hli' with hb
  have hcard : Fintype.card ↥(hli'.extend (Set.subset_univ _)) = M + 1 := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  set e : ↥(hli'.extend (Set.subset_univ _)) ≃ Fin (M + 1) := Fintype.equivFinOfCardEq hcard with he
  refine ⟨b.reindex e, fun z hz => ?_⟩
  have hmem : (μ z : Fin (M + 1) → ℂ) ∈ hli'.extend (Set.subset_univ _) := by
    apply LinearIndepOn.subset_extend hli' (Set.subset_univ _)
    exact ⟨⟨z, hz⟩, rfl⟩
  refine ⟨e ⟨μ z, hmem⟩, ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hb, Basis.coe_extend]

/-- **A μ-Slater state is a mode monomial over the extended basis** `eμ`: since `eμ(idx z) = μ_z`,
the special-basis creators are mode creators of `eμ`, so `generalFlatBandSlaterState μ qs` (with all
modes in `I`) equals `generalModeMonomial eμ (qs ↦ (idx z, σ))`.  This carries the μ-Slater states
into the general occupation basis (`generalOccBasis eμ`), giving their linear independence for
free. -/
theorem generalFlatBandSlaterState_eq_generalModeMonomial
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    (qs : List (Fin (M + 1) × Fin 2)) (hqs : ∀ q ∈ qs, q.1 ∈ I) :
    generalFlatBandSlaterState μ qs
      = generalModeMonomial eμ (qs.map (fun q => (idx q.1, q.2))) := by
  unfold generalFlatBandSlaterState generalModeMonomial
  rw [List.map_map]
  congr 2
  apply List.map_congr_left
  intro q hq
  rw [Function.comp_apply, generalFlatBandCreation, ← hidx q.1 (hqs q hq)]

/-- The **`I`-mode `μ`-Slater Fock submodule**: the span of the `μ`-Slater states whose modes all
lie in the index set `I` (the tight version of `generalFlatBandFockSubmodule`, in which a ground
state actually lives — PR6 builds it from `ker T = span{μ_z}` creations only). -/
noncomputable def generalFlatBandIModeFockSubmodule (I : Finset (Fin (M + 1)))
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) : Submodule ℂ ((Fin (2 * M + 2) → Fin 2) → ℂ) :=
  Submodule.span ℂ
    {v | ∃ qs : List (Fin (M + 1) × Fin 2),
      (∀ q ∈ qs, q.1 ∈ I) ∧ generalFlatBandSlaterState μ qs = v}

/-- An `I`-mode `μ`-Slater state lies in the `I`-mode submodule. -/
theorem generalFlatBandSlaterState_mem_imode {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (qs : List (Fin (M + 1) × Fin 2))
    (hqs : ∀ q ∈ qs, q.1 ∈ I) :
    generalFlatBandSlaterState μ qs ∈ generalFlatBandIModeFockSubmodule I μ :=
  Submodule.subset_span ⟨qs, hqs, rfl⟩

/-- The `I`-mode submodule is invariant under each index-mode creation `â†_{μ_z,σ}` with `z ∈ I`. -/
theorem generalFlatBandCreation_mulVec_mem_imode {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} {z : Fin (M + 1)} (hz : z ∈ I) (σ : Fin 2)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ} (hv : v ∈ generalFlatBandIModeFockSubmodule I μ) :
    (generalFlatBandCreation μ z σ).mulVec v ∈ generalFlatBandIModeFockSubmodule I μ := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨qs, hqs, rfl⟩
    rw [generalFlatBandCreation_mulVec_slaterState]
    refine generalFlatBandSlaterState_mem_imode _ ?_
    intro q hq
    rcases List.mem_cons.mp hq with h | h
    · rw [h]; exact hz
    · exact hqs q h
  · rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx; rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

/-- The `I`-mode submodule is invariant under `Ĉ†_σ(w)` for every `w ∈ span{μ_z}` (= ker T). -/
theorem spinfulCreationFromVector_span_mulVec_mem_imode {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (σ : Fin 2) {w : Fin (M + 1) → ℂ}
    (hw : w ∈ Submodule.span ℂ (Set.range (fun z : I => (μ z.1 : Fin (M + 1) → ℂ))))
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ} (hv : v ∈ generalFlatBandIModeFockSubmodule I μ) :
    (spinfulCreationFromVector M w σ).mulVec v ∈ generalFlatBandIModeFockSubmodule I μ := by
  induction hw using Submodule.span_induction with
  | mem w' hw' =>
    obtain ⟨z, rfl⟩ := hw'
    exact generalFlatBandCreation_mulVec_mem_imode z.2 σ hv
  | zero =>
    rw [spinfulCreationFromVector_zero, Matrix.zero_mulVec]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [spinfulCreationFromVector_add, Matrix.add_mulVec]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [spinfulCreationFromVector_smul, Matrix.smul_mulVec]; exact Submodule.smul_mem _ a hx

/-- A flat-mode eigenbasis monomial lies in the `I`-mode submodule (tight version of PR6). -/
theorem generalModeMonomial_mem_imode {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    (hT : T.IsHermitian) {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (qs : List (Fin (M + 1) × Fin 2))
    (hqs : ∀ q ∈ qs, (eigenbasisAsBasis hT q.1 : Fin (M + 1) → ℂ)
      ∈ Submodule.span ℂ (Set.range (fun z : I => (μ z.1 : Fin (M + 1) → ℂ)))) :
    generalModeMonomial (eigenbasisAsBasis hT) qs ∈ generalFlatBandIModeFockSubmodule I μ := by
  induction qs with
  | nil =>
    have hvac := generalFlatBandSlaterState_mem_imode (I := I) (μ := μ)
      ([] : List (Fin (M + 1) × Fin 2)) (by simp)
    simpa only [generalModeMonomial, generalFlatBandSlaterState, List.map_nil, List.prod_nil]
      using hvac
  | cons q qs' ih =>
    obtain ⟨q1, q2⟩ := q
    rw [← spinfulCreation_mulVec_generalModeMonomial (eigenbasisAsBasis hT) q1 q2 qs']
    exact spinfulCreationFromVector_span_mulVec_mem_imode q2
      (hqs (q1, q2) List.mem_cons_self)
      (ih fun q' hq' => hqs q' (List.mem_cons_of_mem _ hq'))

/-- **A flat-band ground state lies in the `I`-mode `μ`-Slater Fock submodule** (the tight transport
of eq. (11.3.46)): the flat-supported eigenbasis monomials use only flat eigenvectors, each in
`ker T = span{μ_z}`, so the `I`-mode submodule's invariance under index-mode creation carries `Φ`
into it. -/
theorem flatBand_groundState_mem_imode {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ) (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    Φ ∈ generalFlatBandIModeFockSubmodule I μ := by
  have heig : ∀ j : Fin (M + 1), hT.1.eigenvalues j = 0 →
      (eigenbasisAsBasis hT.1 j : Fin (M + 1) → ℂ)
        ∈ Submodule.span ℂ (Set.range (fun z : I => (μ z.1 : Fin (M + 1) → ℂ))) := by
    intro j hj
    rw [← ker_mulVecLin_eq_span_specialBasis hbasis, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      eigenbasisAsBasis_mulVec hT.1 j, hj, Complex.ofReal_zero, zero_smul]
  refine (Submodule.span_le.mpr ?_) (flatBand_groundState_atFilling_mem_flatFockSpan hT U hU hΦ)
  rintro _ ⟨g, hf, _, rfl⟩
  refine generalModeMonomial_mem_imode (I := I) hT.1 _ fun q hq => ?_
  have hgq : g q = 1 := by
    have := Finset.mem_toList.mp hq
    simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
  exact heig q.1 (hf q.1 q.2 (by rw [← hgq]))

end LatticeSystem.Fermion

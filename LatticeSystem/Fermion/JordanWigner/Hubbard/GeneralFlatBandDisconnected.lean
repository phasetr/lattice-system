import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandDisconnectedCore

/-!
# The disconnected flat-band ground subspace and Theorem 11.17 (Tasaki §11.3.4)

The `⟹` direction of Theorem 11.17 (ferromagnetic `⟹` connected) and the capstone equivalence.
A spin-separated μ-Slater (opposite-spin modes with disjoint site support) is a ground state; more
generally an edge-swap-invariant canonical-Slater sum is (the converse of the eq. (11.3.49)
characterization, via the interaction kill `generalCDownUp x Φ = 0`).  For a disconnected basis a
non-trivial cut `(A, Aᶜ)` then yields `(|A|+1)(|Aᶜ|+1) > D₀+1` independent per-block weight ground
states, so `finrank > D₀+1`, contradicting the maximal-spin multiplet.  Together with the `⇐`
direction (`generalFlatBand_connected_isMaximalSpinMultiplet`, in `GeneralFlatBandMultiplet.lean`)
this discharges the axiom as the proved theorem `generalFlatBand_theorem_11_17`.

Split from `GeneralFlatBandMultiplet.lean` (build-speed refactor): the `⇐` multiplet construction
stays there; this file holds the `⇒` disconnected machinery and the capstone.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §11.3.4, Theorem 11.17, pp. 410-412.  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators

variable {M : ℕ}

open scoped ComplexOrder in
/-- **A disconnected special basis has ground dimension exceeding `D₀+1`**: the `(|A|+1)(|Aᶜ|+1)`
per-block weight states `W_{p,q}` of a non-trivial cut are linearly independent ground states, so
`finrank > D₀+1`.  Independence is read off the occupation basis: at the index config of a
representative of fiber `(p₀,q₀)`, only `W_{p₀,q₀}` has a nonzero coordinate (the index config of a
canonical creation list determines its spin configuration,
`idxConfigOf_flatBandSpinConfigList_inj_gen`,
and the per-block up-counts pick out the fiber).  This is the contradiction with the maximal-spin
multiplet's `finrank = D₀+1`, giving the `⟹` direction of Theorem 11.17. -/
theorem generalFlatBand_disconnected_finrank_gt
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hnc : ¬ generalFlatBandBasisConnected I μ) (hne : I.Nonempty) :
    generalFlatBandDim T + 1 < Module.finrank ℂ ↥(generalFlatBandGroundSubmodule T U) := by
  classical
  obtain ⟨A, hAne, hAcne, hcut⟩ := exists_disconnection_cut_of_not_connected hnc hne
  obtain ⟨eμ, heμ⟩ := exists_extended_special_basis hbasis
  choose! idx hidx using heμ
  set G := generalFlatBandGroundSubmodule T U with hG
  set ind : ℕ → ℕ → (I → Fin 2) → ℂ := fun p q s =>
    if (A.filter (fun z => s z = 0)).card = p ∧ (Aᶜ.filter (fun z => s z = 0)).card = q
      then 1 else 0 with hind
  set W : Fin (A.card + 1) × Fin (Aᶜ.card + 1) → (Fin (2 * M + 2) → Fin 2) → ℂ :=
    fun pq => ∑ s : I → Fin 2, ind pq.1 pq.2 s • generalFlatBandSlaterState μ
      (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)) with hW
  have hWmem : ∀ pq, W pq ∈ G := fun pq =>
    generalFlatBand_blockWeightState_mem_groundSubmodule hbasis hT U hidx A hcut pq.1 pq.2
  have hWLI : LinearIndependent ℂ (fun pq => (⟨W pq, hWmem pq⟩ : G)) := by
    apply LinearIndependent.of_comp G.subtype
    rw [Fintype.linearIndependent_iff]
    intro c hc pq₀
    obtain ⟨s₀, hs₀A, hs₀B⟩ := exists_blockUpCount_config A (Nat.lt_succ_iff.mp pq₀.1.2)
      (Nat.lt_succ_iff.mp pq₀.2.2)
    set t₀ : Fin (M + 1) → Fin 2 := fun z => if h : z ∈ I then s₀ ⟨z, h⟩ else 0 with ht₀
    set g₀ := idxConfigOf idx (flatBandSpinConfigList I t₀) with hg₀
    set z₀ := (generalOccBasis eμ).repr
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I t₀)) g₀ with hz₀def
    have hz₀ne : z₀ ≠ 0 := by
      rw [hz₀def, hg₀]
      exact generalFlatBandSlaterState_repr_self_ne_zero hbasis eμ idx hidx
        (flatBandSpinConfigList I t₀) (flatBandSpinConfigList_nodup I t₀)
        (fun q hq => flatBandSpinConfigList_mem_fst_mem I t₀ hq)
    have hreprzero : ∀ s : I → Fin 2, s ≠ s₀ → (generalOccBasis eμ).repr
        (generalFlatBandSlaterState μ (flatBandSpinConfigList I
          (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))) g₀ = 0 := by
      intro s hss
      obtain ⟨z, _, hzeq⟩ := generalFlatBandSlaterState_over_I_repr hbasis eμ idx hidx
        (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))
        (flatBandSpinConfigList_nodup I _)
        (fun q hq => flatBandSpinConfigList_mem_fst_mem I _ hq) g₀
      rw [hzeq, if_neg, mul_zero]
      intro hcfg
      refine hss (funext fun w => ?_)
      have hw := (idxConfigOf_flatBandSpinConfigList_inj_gen hbasis hidx
        (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0) t₀ subset_rfl subset_rfl hcfg).2 w.1 w.2
      simpa only [ht₀, dif_pos w.2, Subtype.coe_eta] using hw
    have hind0 : ∀ pq : Fin (A.card + 1) × Fin (Aᶜ.card + 1),
        ind pq.1 pq.2 s₀ = if pq = pq₀ then (1 : ℂ) else 0 := by
      intro pq
      simp only [hind, hs₀A, hs₀B]
      by_cases hpq : pq = pq₀
      · subst hpq; simp
      · rw [if_neg, if_neg hpq]
        rintro ⟨h1, h2⟩
        exact hpq (Prod.ext (Fin.val_injective h1.symm) (Fin.val_injective h2.symm))
    have hWrepr : ∀ pq : Fin (A.card + 1) × Fin (Aᶜ.card + 1),
        (generalOccBasis eμ).repr (W pq) g₀ = (if pq = pq₀ then z₀ else 0) := by
      intro pq
      rw [hW, map_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single s₀]
      · rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← ht₀, ← hz₀def, hind0 pq]
        split_ifs <;> simp
      · intro s _ hss
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hreprzero s hss, mul_zero]
      · intro h; exact absurd (Finset.mem_univ s₀) h
    have hc' : (∑ pq, c pq • W pq) = 0 := hc
    have hc0 : (generalOccBasis eμ).repr (∑ pq, c pq • W pq) g₀ = 0 := by
      rw [hc', map_zero, Finsupp.zero_apply]
    rw [map_sum, Finsupp.finset_sum_apply] at hc0
    simp_rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hWrepr] at hc0
    rw [Finset.sum_eq_single pq₀ (fun pq _ hpq => by rw [if_neg hpq, mul_zero])
      (fun h => absurd (Finset.mem_univ pq₀) h), if_pos rfl] at hc0
    exact (mul_eq_zero.mp hc0).resolve_right hz₀ne
  have hcard := hWLI.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  calc generalFlatBandDim T + 1 = I.card + 1 := by rw [hbasis.1]
    _ < (A.card + 1) * (Aᶜ.card + 1) := disconnection_cut_card_lt A hAne hAcne
    _ ≤ Module.finrank ℂ ↥G := hcard

open scoped ComplexOrder in
/-- **Tasaki Theorem 11.17 (connectivity form of flat-band ferromagnetism)** — discharged from the
axiom (Issue #4363).  For a special basis `{μ_z}` of the flat band (Lemma 11.16), the `D₀`-electron
Hubbard model is saturated-ferromagnetic (its ground subspace is the `(D₀+1)`-fold maximal-spin
multiplet, `generalFlatBandFerromagnetic`) **iff** the basis is connected.

`⇐` (connected ⟹ multiplet) is `generalFlatBand_connected_isMaximalSpinMultiplet`: the SU(2)
lowering tower of the all-up μ-Slater gives `finrank ≥ D₀+1`, the eq. (11.3.49) connectivity
induction gives `finrank ≤ D₀+1`, and the tower spans the ground subspace as `(Ŝ_tot)²`-eigenstates
at the maximal spin.  `⇒` is the contrapositive: a disconnected basis admits a non-trivial cut whose
`(|A|+1)(|Aᶜ|+1) > D₀+1` per-block weight states are independent ground states
(`generalFlatBand_disconnected_finrank_gt`), so `finrank > D₀+1` and the multiplet's
`finrank = D₀+1`
fails.  Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.,
Springer, 2020), §11.3.4, Theorem 11.17, pp. 410–412. -/
theorem generalFlatBand_theorem_11_17 (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ)
    (hT : T.PosSemidef) (hD0 : 0 < generalFlatBandDim T) (hU : 0 < U)
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ) :
    generalFlatBandFerromagnetic T U ↔ generalFlatBandBasisConnected I μ := by
  refine ⟨fun hferro => ?_, fun hconn =>
    generalFlatBand_connected_isMaximalSpinMultiplet hbasis hT U hU hconn⟩
  by_contra hnc
  have hne : I.Nonempty := Finset.card_pos.mp (hbasis.1.symm ▸ hD0)
  have hgt := generalFlatBand_disconnected_finrank_gt hbasis hT U hnc hne
  have hfin : Module.finrank ℂ ↥(generalFlatBandGroundSubmodule T U) = generalFlatBandDim T + 1 :=
    hferro.1
  omega

end LatticeSystem.Fermion

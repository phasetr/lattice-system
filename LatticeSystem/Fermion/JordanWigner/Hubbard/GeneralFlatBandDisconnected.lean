import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandMultiplet

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
/-- **The kinetic operator annihilates *every* μ-Slater state** (any spin configuration `σ`, not
just all-up): the kinetic kill of `hubbardKinetic_mulVec_allUpSlater_eq_zero` is independent of the
spins.  Factor `T = Cᴴ C`; each Gram-mode annihilation `Ĉ_s(C_k)` kills the Slater because every
occupied mode `μ_z` (`z ∈ I`) lies in `ker T = ker C`, regardless of its spin label. -/
theorem hubbardKinetic_mulVec_spinConfigSlater_eq_zero
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (σ : Fin (M + 1) → Fin 2) :
    (hubbardKinetic M T).mulVec
        (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ)) = 0 := by
  obtain ⟨C, hC, hTC⟩ := LatticeSystem.Math.exists_posSemidef_sq_eq_of_posSemidef hT
  have hTCH : T = Cᴴ * C := by rw [hTC, hC.isHermitian.eq]
  set v := generalFlatBandSlaterState μ (flatBandSpinConfigList I σ) with hv
  have hkerC : ∀ z ∈ I, C.mulVec (μ z) = 0 := fun z hz => by
    have hTz : (Cᴴ * C).mulVec (μ z) = 0 := by rw [← hTCH]; exact hbasis.2.1 z hz
    have hmem : μ z ∈ LinearMap.ker (Cᴴ * C).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hTz
    rw [Matrix.ker_mulVecLin_conjTranspose_mul_self] at hmem
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem
  have hCk : ∀ (s : Fin 2) (k : Fin (M + 1)),
      (spinfulAnnihilationFromVector M (fun j => C k j) s).mulVec v = 0 := fun s k =>
    spinfulAnnihilationFromVector_mulVec_generalFlatBandSlaterState_eq_zero_of_orthogonal
      μ (fun j => C k j) s _ (fun q hq => by
        have hk := congrFun (hkerC q.1 (flatBandSpinConfigList_mem_fst_mem I _ hq)) k
        simpa [Matrix.mulVec, dotProduct] using hk)
  rw [hTCH, hubbardKinetic_conjTranspose_mul_self_eq_gram_sum, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [← Matrix.mulVec_mulVec, hCk s k, Matrix.mulVec_zero]

/-- **The site double-annihilation `ĉ_{x,↓}ĉ_{x,↑}` kills a spin-separated μ-Slater**: if at every
site `x` opposite-spin modes have disjoint support (`σ z ≠ σ w ⟹ μ_z(x)μ_w(x) = 0`), then no site
carries both an up- and a down-electron, so `ĉ_{x,↓}ĉ_{x,↑}` annihilates the Slater.  Expanding the
double peel (`cDownUp_canonical_eq_doublePeel`), every term pairs an up-mode (outer, `μ_{q_i}(x)`)
with a down-mode (inner, `μ_{q_j}(x)`); by separation their product vanishes. -/
theorem generalCDownUp_mulVec_spinSeparatedSlater_eq_zero
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (I : Finset (Fin (M + 1)))
    (σ : Fin (M + 1) → Fin 2) (x : Fin (M + 1))
    (hsep : ∀ z ∈ I, ∀ w ∈ I, σ z ≠ σ w → μ z x * μ w x = 0) :
    (generalCDownUp M x).mulVec
        (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ)) = 0 := by
  rw [cDownUp_canonical_eq_doublePeel]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rcases eq_or_ne ((flatBandSpinConfigList I σ).get i).2 0 with hi | hi
  · rw [if_pos hi]
    suffices h : μ ((flatBandSpinConfigList I σ).get i).1 x •
        (∑ j : Fin ((flatBandSpinConfigList I σ).eraseIdx i).length,
          generalFlatBandPeelTerm μ x 1 ((flatBandSpinConfigList I σ).eraseIdx i) j) = 0 by
      rw [h, smul_zero]
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [generalFlatBandPeelTerm]
    rcases eq_or_ne (((flatBandSpinConfigList I σ).eraseIdx i).get j).2 1 with hj | hj
    · rw [if_pos hj]
      have heL : ((flatBandSpinConfigList I σ).eraseIdx i).get j ∈ flatBandSpinConfigList I σ :=
        List.mem_of_mem_eraseIdx (List.get_mem _ j)
      have h1 : σ ((flatBandSpinConfigList I σ).get i).1 = 0 := by
        rw [← flatBandSpinConfigList_get_snd_eq I σ i]; exact hi
      have h2 : σ (((flatBandSpinConfigList I σ).eraseIdx i).get j).1 = 1 := by
        rw [← flatBandSpinConfigList_mem_snd_eq I σ heL]; exact hj
      have hzero : μ ((flatBandSpinConfigList I σ).get i).1 x *
          μ (((flatBandSpinConfigList I σ).eraseIdx i).get j).1 x = 0 :=
        hsep _ (flatBandSpinConfigList_mem_fst_mem I σ (List.get_mem _ i)) _
          (flatBandSpinConfigList_mem_fst_mem I σ heL) (by rw [h1, h2]; decide)
      rw [smul_smul, smul_smul, mul_right_comm, hzero, zero_mul, zero_smul]
    · rw [if_neg hj, zero_smul, smul_zero, smul_zero]
  · rw [if_neg hi, zero_smul, smul_zero]

open scoped ComplexOrder in
/-- **A spin-separated μ-Slater is a flat-band ground state**: for any spin configuration `σ` whose
opposite-spin modes have disjoint site support (`σ z ≠ σ w ⟹ ∀ x, μ_z(x)μ_w(x) = 0`), the Slater
state is in `generalFlatBandGroundSubmodule`.  The kinetic part annihilates it
(`hubbardKinetic_mulVec_spinConfigSlater_eq_zero`); the interaction
`Σ_x U·n̂_{x↑}n̂_{x↓} = Σ_x U·(ĉ_{x↓}ĉ_{x↑})ᴴ(ĉ_{x↓}ĉ_{x↑})` annihilates it because no site is
doubly
occupied (`generalCDownUp_mulVec_spinSeparatedSlater_eq_zero`); and `N̂_tot` eigenvalue is `D₀`.
For a disconnected basis a component-colouring gives such a `σ` lying outside the maximal-spin
tower,
the seed of the `⟹` direction of Theorem 11.17. -/
theorem generalFlatBandSlaterState_spinSeparated_mem_groundSubmodule
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (σ : Fin (M + 1) → Fin 2)
    (hsep : ∀ z ∈ I, ∀ w ∈ I, σ z ≠ σ w → ∀ x, μ z x * μ w x = 0) :
    generalFlatBandSlaterState μ (flatBandSpinConfigList I σ)
      ∈ generalFlatBandGroundSubmodule T U := by
  simp only [generalFlatBandGroundSubmodule, Submodule.mem_inf, LinearMap.mem_ker,
    Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  refine ⟨?_, ?_⟩
  · have hint : (hubbardOnSiteInteraction M (U : ℂ)).mulVec
        (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ)) = 0 := by
      unfold hubbardOnSiteInteraction
      rw [Matrix.sum_mulVec]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      have hdo : (hubbardDoubleOccupancy M x).mulVec
          (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ)) = 0 := by
        rw [hubbardDoubleOccupancy_eq_conjTranspose_mul_self_general, ← Matrix.mulVec_mulVec,
          generalCDownUp_mulVec_spinSeparatedSlater_eq_zero μ I σ x
            (fun z hz w hw hne => hsep z hz w hw hne x), Matrix.mulVec_zero]
      rw [Matrix.smul_mulVec,
        show fermionUpNumber M x * fermionDownNumber M x = hubbardDoubleOccupancy M x from rfl,
        hdo, smul_zero]
    rw [hubbardHamiltonian, Matrix.add_mulVec,
      hubbardKinetic_mulVec_spinConfigSlater_eq_zero hbasis hT, hint, add_zero]
  · rw [fermionTotalNumber_mulVec_generalFlatBandSlaterState, flatBandSpinConfigList_length,
      hbasis.1]

/-- **A disconnected special basis splits into a non-trivial cut with no crossing μ-overlap**: if
the
basis graph is not connected (and `I` is nonempty), there is a subset `A` of the index set with `A`
and its complement both nonempty such that opposite-side modes have disjoint site support
(`z ∈ A`, `w ∉ A` ⟹ `∀ x, μ_z(x)μ_w(x) = 0`).  `A` is the connected component of a vertex `a` that
fails to reach some `b`; a crossing μ-overlap would be an edge `z ~ w`, making `w` reachable from
`a` — contradiction.  This is the cut underlying the `finrank > D₀+1` bound of the `⟹` direction. -/
theorem exists_disconnection_cut_of_not_connected {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hnc : ¬ generalFlatBandBasisConnected I μ)
    (hne : I.Nonempty) :
    ∃ A : Finset ↥I, A.Nonempty ∧ Aᶜ.Nonempty ∧
      ∀ z ∈ A, ∀ w ∈ Aᶜ, ∀ x, μ z.1 x * μ w.1 x = 0 := by
  classical
  have hnonempty : Nonempty ↥I := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hnp : ¬ (generalFlatBandBasisGraph I μ).Preconnected := fun hp =>
    hnc ((SimpleGraph.connected_iff _).mpr ⟨hp, hnonempty⟩)
  rw [SimpleGraph.Preconnected] at hnp
  push Not at hnp
  obtain ⟨a, b, hab⟩ := hnp
  refine ⟨Finset.univ.filter (fun z => (generalFlatBandBasisGraph I μ).Reachable a z),
    ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl a⟩⟩, ⟨b, ?_⟩, ?_⟩
  · rw [Finset.mem_compl, Finset.mem_filter]
    exact fun h => hab h.2
  · intro z hz w hw x
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_compl, Finset.mem_filter] at hw
    by_contra hxne
    have hzx : μ z.1 x ≠ 0 := fun h => hxne (by rw [h, zero_mul])
    have hwx : μ w.1 x ≠ 0 := fun h => hxne (by rw [h, mul_zero])
    have hzw : z.1 ≠ w.1 := fun h =>
      hw ⟨Finset.mem_univ _, (Subtype.ext h : z = w) ▸ hz.2⟩
    exact hw ⟨Finset.mem_univ _, hz.2.trans
      (SimpleGraph.Adj.reachable (⟨hzw, x, hzx, hwx⟩ : (generalFlatBandBasisGraph I μ).Adj z w))⟩

/-- **The 2-block cut beats the maximal-spin dimension**: for a non-trivial cut `(A, Aᶜ)` of the
`D₀`-element index set, `(|A|+1)(|Aᶜ|+1) > D₀ + 1`.  Since `|A|, |Aᶜ| ≥ 1` and `|A|+|Aᶜ| = D₀`, the
product `|A||Aᶜ| + D₀ + 1` strictly exceeds `D₀ + 1`.  The per-block weight states of a disconnected
basis number `(|A|+1)(|Aᶜ|+1)`, so this is the contradiction with `finrank = D₀ + 1`. -/
theorem disconnection_cut_card_lt {I : Finset (Fin (M + 1))} (A : Finset ↥I)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    I.card + 1 < (A.card + 1) * (Aᶜ.card + 1) := by
  have hcard : A.card + Aᶜ.card = I.card := by
    rw [Finset.card_add_card_compl A, Fintype.card_coe]
  have h1 : 1 ≤ A.card := hA.card_pos
  have h2 : 1 ≤ Aᶜ.card := hAc.card_pos
  nlinarith [hcard, h1, h2]

/-- **Two-hole-target coordinate kill for an edge-swap-invariant `D`-sum**: at the `(a,b)`-emptied
occupation target `g_ab`, the `D`-weighted sum of `ĉ_{x↓}ĉ_{x↑}`-coordinates over all spin configs
vanishes (for `D` edge-swap-invariant).  The sum collapses (`cDownUp_canonicalSum_eq_two_terms`) to
`D(σ)·coord_σ + D(σ')·coord_σ'`; the coordinates are negatives (`..._twoHole_swap_eq_neg`) and the
two-hole coordinate carries a `μ_a(x)μ_b(x)` factor (`cDownUp_canonical_repr_twoHole`), so either
`a,b` connect at `x` (giving an edge `⟨a⟩ ~ ⟨b⟩`, whence `D(σ) = D(σ')` and the terms cancel) or the
coordinate vanishes.  This is the reverse of the eq. (11.3.49) Marshall-sign derivation, used to put
the per-block weight states of a disconnected basis into the ground subspace. -/
theorem cDownUp_canonicalSlaterSum_repr_twoHole_eq_zero_of_edgeSwap_invariant
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) {a b : Fin (M + 1)} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b)
    (hσa : σ a = 0) (hσb : σ b = 1) (D : (I → Fin 2) → ℂ)
    (hedge : ∀ {z z' : ↥I}, (generalFlatBandBasisGraph I μ).Adj z z' →
      ∀ s : I → Fin 2, D s = D (s ∘ ⇑(Equiv.swap z z'))) :
    ∑ s : I → Fin 2, D s * (generalOccBasis eμ).repr
        ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ
          (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))))
        (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) = 0 := by
  have hcanσ : flatBandSpinConfigList I
      (fun z => if h : z ∈ I then (fun z : I => σ z.1) ⟨z, h⟩ else 0)
        = flatBandSpinConfigList I σ :=
    flatBandSpinConfigList_congr I _ σ (fun z hz => by simp only [dif_pos hz])
  have hcanσ' : flatBandSpinConfigList I
      (fun z => if h : z ∈ I then (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1) ⟨z, h⟩ else 0)
        = flatBandSpinConfigList I (σ ∘ ⇑(Equiv.swap a b)) :=
    flatBandSpinConfigList_congr I _ _ (fun z hz => by simp only [dif_pos hz])
  rw [cDownUp_canonicalSum_eq_two_terms hbasis hidx σ x ha hb hab hσa hσb D, hcanσ, hcanσ']
  set cσ := (generalOccBasis eμ).repr ((generalCDownUp M x).mulVec
    (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ)))
    (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) with hcσdef
  set cσ' := (generalOccBasis eμ).repr ((generalCDownUp M x).mulVec
    (generalFlatBandSlaterState μ (flatBandSpinConfigList I (σ ∘ ⇑(Equiv.swap a b)))))
    (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) with hcσ'def
  have hneg : cσ = -cσ' :=
    cDownUp_canonical_repr_twoHole_swap_eq_neg hbasis hidx σ x ha hb hab hσa hσb
  by_cases hμ : μ a x = 0 ∨ μ b x = 0
  · have hcσ0 : cσ = 0 := by
      rw [hcσdef, cDownUp_canonical_repr_twoHole hbasis hidx σ x ha hb hab hσa hσb]
      rcases hμ with h | h <;> simp [h]
    have hcσ'0 : cσ' = 0 := by
      have h := hneg; rw [hcσ0] at h; exact neg_eq_zero.mp h.symm
    rw [hcσ0, hcσ'0, mul_zero, mul_zero, add_zero]
  · push Not at hμ
    have hadj : (generalFlatBandBasisGraph I μ).Adj ⟨a, ha⟩ ⟨b, hb⟩ :=
      ⟨hab, x, hμ.1, hμ.2⟩
    have hswapcompat : ∀ z : ↥I,
        ((Equiv.swap (⟨a, ha⟩ : ↥I) ⟨b, hb⟩) z).1 = Equiv.swap a b z.1 := by
      intro z
      rcases eq_or_ne z ⟨a, ha⟩ with hz | hz
      · subst hz; simp [Equiv.swap_apply_left]
      · rcases eq_or_ne z ⟨b, hb⟩ with hz2 | hz2
        · subst hz2; simp [Equiv.swap_apply_right]
        · rw [Equiv.swap_apply_of_ne_of_ne hz hz2,
            Equiv.swap_apply_of_ne_of_ne (fun h => hz (Subtype.ext h))
              (fun h => hz2 (Subtype.ext h))]
    have hsσ'eq : (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1)
        = (fun z : I => σ z.1) ∘ ⇑(Equiv.swap (⟨a, ha⟩ : ↥I) ⟨b, hb⟩) := by
      funext z; simp only [Function.comp_apply]; rw [hswapcompat z]
    have hDeq : D (fun z : I => σ z.1) = D (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1) := by
      rw [hsσ'eq]; exact hedge hadj (fun z : I => σ z.1)
    rw [hDeq, hneg]; ring

/-- **Off-target coordinate kill for a `D`-sum**: at an occupation target `g` that is *not* a
`(D₀-2)`-emptied two-hole config of any pair, the `D`-weighted sum of `ĉ_{x↓}ĉ_{x↑}`-coordinates
vanishes.  Expanding the double peel (`cDownUp_canonical_repr_eq_sum`), every inner rest-Slater
coordinate is a Kronecker delta (`generalFlatBandSlaterState_over_I_repr`) at the occupation config
of the twice-erased canonical list
`((canonical).eraseIdx i).eraseIdx j = canonical((I.erase a).erase b) σ`
(`flatBandSpinConfigList_eraseIdx_eraseIdx`); since `g` matches no such config (`hnot`), every delta
is zero.  Together with the two-hole-target kill this gives `generalCDownUp x Φ = 0`. -/
theorem cDownUp_canonicalSlaterSum_repr_eq_zero_of_not_twoHoleTarget
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (x : Fin (M + 1))
    (D : (I → Fin 2) → ℂ) (g : Fin (M + 1) × Fin 2 → Fin 2)
    (hnot : ∀ (σ : Fin (M + 1) → Fin 2) (a b : Fin (M + 1)), a ∈ I → b ∈ I → a ≠ b →
      g ≠ idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) :
    ∑ s : I → Fin 2, D s * (generalOccBasis eμ).repr
        ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ
          (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)))) g = 0 := by
  refine Finset.sum_eq_zero (fun s _ => ?_)
  set σ : Fin (M + 1) → Fin 2 := fun z => if h : z ∈ I then s ⟨z, h⟩ else 0 with hσdef
  suffices h : (generalOccBasis eμ).repr ((generalCDownUp M x).mulVec
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ))) g = 0 by rw [h, mul_zero]
  rw [cDownUp_canonical_repr_eq_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hinner : (∑ j : Fin ((flatBandSpinConfigList I σ).eraseIdx (i : ℕ)).length,
      ((-1 : ℂ) ^ (j : ℕ)) *
        ((if (((flatBandSpinConfigList I σ).eraseIdx (i : ℕ)).get j).2 = 1 then
            μ (((flatBandSpinConfigList I σ).eraseIdx (i : ℕ)).get j).1 x else 0) *
          (generalOccBasis eμ).repr (generalFlatBandSlaterState μ
            (((flatBandSpinConfigList I σ).eraseIdx (i : ℕ)).eraseIdx (j : ℕ))) g)) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hnd : (((flatBandSpinConfigList I σ).eraseIdx (i : ℕ)).eraseIdx (j : ℕ)).Nodup :=
      (flatBandSpinConfigList_eraseIdx_nodup I σ (i : ℕ)).eraseIdx (j : ℕ)
    have hmemI : ∀ q ∈ ((flatBandSpinConfigList I σ).eraseIdx (i : ℕ)).eraseIdx (j : ℕ), q.1 ∈ I :=
      fun q hq => flatBandSpinConfigList_mem_fst_mem I σ
        (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx hq))
    obtain ⟨z, _, hz⟩ := generalFlatBandSlaterState_over_I_repr hbasis eμ idx hidx
      (((flatBandSpinConfigList I σ).eraseIdx (i : ℕ)).eraseIdx (j : ℕ)) hnd hmemI g
    set a : Fin (M + 1) := ((flatBandSpinConfigList I σ)[(i : ℕ)]).1 with ha_def
    have heq : (flatBandSpinConfigList I σ).eraseIdx (i : ℕ)
        = flatBandSpinConfigList (I.erase a) σ :=
      flatBandSpinConfigList_eraseIdx I σ i.2
    have hjlt : (j : ℕ) < (flatBandSpinConfigList (I.erase a) σ).length := by
      rw [← heq]; exact j.2
    set b : Fin (M + 1) := ((flatBandSpinConfigList (I.erase a) σ)[(j : ℕ)]).1 with hb_def
    have hrest : ((flatBandSpinConfigList I σ).eraseIdx (i : ℕ)).eraseIdx (j : ℕ)
        = flatBandSpinConfigList ((I.erase a).erase b) σ :=
      flatBandSpinConfigList_eraseIdx_eraseIdx I σ i.2 hjlt
    have ha : a ∈ I := flatBandSpinConfigList_mem_fst_mem I σ (List.getElem_mem _)
    have hbe : b ∈ I.erase a := flatBandSpinConfigList_mem_fst_mem _ σ (List.getElem_mem _)
    have hrepr0 : (generalOccBasis eμ).repr (generalFlatBandSlaterState μ
        (((flatBandSpinConfigList I σ).eraseIdx (i : ℕ)).eraseIdx (j : ℕ))) g = 0 := by
      rw [hz]; split_ifs with hc
      · exact absurd ((hc.symm).trans (congrArg (idxConfigOf idx) hrest))
          (hnot σ a b ha (Finset.mem_of_mem_erase hbe) (Ne.symm (Finset.ne_of_mem_erase hbe)))
      · rw [mul_zero]
    rw [hrepr0, mul_zero, mul_zero]
  rw [hinner, mul_zero, mul_zero]

/-- **The site double-annihilation kills an edge-swap-invariant `D`-sum**: `ĉ_{x↓}ĉ_{x↑} Φ = 0`
for `Φ = Σ_s D(s)·Slater(canonical I (extend s))` with `D` edge-swap-invariant.  Reduce (via
`generalOccBasis` injectivity) to every occupation coordinate vanishing; at each target `g`, the
`D`-weighted coordinate sum is killed either by the two-hole-target lemma (`g` a `(D₀-2)`-emptied
config of a pair, where edge-swap invariance forces the cancellation) or the off-target lemma
(otherwise).  A target config is spin-independent in `σ a`, `σ b`, so a witness with `σa=0, σb=1`
exists whenever any does. -/
theorem generalCDownUp_mulVec_canonicalSlaterSum_eq_zero_of_edgeSwap_invariant
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (x : Fin (M + 1))
    (D : (I → Fin 2) → ℂ)
    (hedge : ∀ {z z' : ↥I}, (generalFlatBandBasisGraph I μ).Adj z z' →
      ∀ s : I → Fin 2, D s = D (s ∘ ⇑(Equiv.swap z z'))) :
    (generalCDownUp M x).mulVec (∑ s : I → Fin 2, D s • generalFlatBandSlaterState μ
        (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))) = 0 := by
  classical
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul]
  refine (generalOccBasis eμ).repr.map_eq_zero_iff.mp (Finsupp.ext (fun g => ?_))
  rw [Finsupp.zero_apply, map_sum, Finsupp.finset_sum_apply]
  simp_rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hg : ∃ (σ : Fin (M + 1) → Fin 2) (a b : Fin (M + 1)),
      a ∈ I ∧ b ∈ I ∧ a ≠ b ∧ g = idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)
  · obtain ⟨σ, a, b, ha, hb, hab, hgeq⟩ := hg
    set σ'' : Fin (M + 1) → Fin 2 := Function.update (Function.update σ a 0) b 1 with hσ''
    have hσ''a : σ'' a = 0 := by
      rw [hσ'', Function.update_of_ne hab, Function.update_self]
    have hσ''b : σ'' b = 1 := by rw [hσ'']; exact Function.update_self _ _ _
    have hcongr : flatBandSpinConfigList ((I.erase a).erase b) σ
        = flatBandSpinConfigList ((I.erase a).erase b) σ'' :=
      flatBandSpinConfigList_congr _ σ σ'' (fun z hz => by
        rw [hσ'', Function.update_of_ne (Finset.ne_of_mem_erase hz),
          Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz))])
    rw [hgeq, hcongr]
    exact cDownUp_canonicalSlaterSum_repr_twoHole_eq_zero_of_edgeSwap_invariant hbasis hidx σ'' x
      ha hb hab hσ''a hσ''b D hedge
  · push Not at hg
    exact cDownUp_canonicalSlaterSum_repr_eq_zero_of_not_twoHoleTarget hbasis hidx x D g
      (fun σ a b ha hb hab => hg σ a b ha hb hab)

open scoped ComplexOrder in
/-- **An edge-swap-invariant canonical-Slater sum is a flat-band ground state**: for `D` invariant
under every basis-graph edge transposition, `Φ = Σ_s D(s)·Slater(canonical I (extend s))` lies in
`generalFlatBandGroundSubmodule`.  Kinetic kill is per-Slater
(`hubbardKinetic_mulVec_spinConfigSlater_eq_zero`); interaction kill follows from
`ĉ_{x↓}ĉ_{x↑} Φ = 0` via the double-occupancy factorization; and `N̂_tot Φ = D₀ Φ`.  This is the
converse of the eq. (11.3.49) ground-state characterization, used to place the per-block weight
states of a disconnected basis into the ground subspace. -/
theorem canonicalSlaterSum_mem_groundSubmodule_of_edgeSwap_invariant
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)}
    {idx : Fin (M + 1) → Fin (M + 1)} (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    (D : (I → Fin 2) → ℂ)
    (hedge : ∀ {z z' : ↥I}, (generalFlatBandBasisGraph I μ).Adj z z' →
      ∀ s : I → Fin 2, D s = D (s ∘ ⇑(Equiv.swap z z'))) :
    (∑ s : I → Fin 2, D s • generalFlatBandSlaterState μ
        (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)))
      ∈ generalFlatBandGroundSubmodule T U := by
  simp only [generalFlatBandGroundSubmodule, Submodule.mem_inf, LinearMap.mem_ker,
    Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  refine ⟨?_, ?_⟩
  · have hK : (hubbardKinetic M T).mulVec (∑ s : I → Fin 2, D s • generalFlatBandSlaterState μ
        (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))) = 0 := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_eq_zero (fun s _ => ?_)
      rw [Matrix.mulVec_smul, hubbardKinetic_mulVec_spinConfigSlater_eq_zero hbasis hT, smul_zero]
    have hInt : (hubbardOnSiteInteraction M (U : ℂ)).mulVec
        (∑ s : I → Fin 2, D s • generalFlatBandSlaterState μ
          (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))) = 0 := by
      unfold hubbardOnSiteInteraction
      rw [Matrix.sum_mulVec]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      have hcd := generalCDownUp_mulVec_canonicalSlaterSum_eq_zero_of_edgeSwap_invariant
        hbasis hidx x D hedge
      rw [Matrix.smul_mulVec,
        show fermionUpNumber M x * fermionDownNumber M x = hubbardDoubleOccupancy M x from rfl,
        hubbardDoubleOccupancy_eq_conjTranspose_mul_self_general, ← Matrix.mulVec_mulVec, hcd,
        Matrix.mulVec_zero, smul_zero]
    rw [hubbardHamiltonian, Matrix.add_mulVec, hK, hInt, add_zero]
  · rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Matrix.mulVec_smul, fermionTotalNumber_mulVec_generalFlatBandSlaterState,
      flatBandSpinConfigList_length, hbasis.1, smul_comm]

/-- **An in-block transposition preserves the up-count of a block**: for `z, z'` both in `T` or
both outside `T`, the number of up-spins of `s ∘ swap z z'` on `T` equals that of `s`.  If both lie
in `T`, `swap z z'` is a bijection of `T` permuting the count; if both lie outside, `swap z z'`
fixes `T` pointwise. -/
theorem upCountOn_comp_swap_eq {I : Finset (Fin (M + 1))} (T : Finset ↥I) (s : ↥I → Fin 2)
    {z z' : ↥I} (h : (z ∈ T ∧ z' ∈ T) ∨ (z ∉ T ∧ z' ∉ T)) :
    (T.filter (fun w => (s ∘ ⇑(Equiv.swap z z')) w = 0)).card
      = (T.filter (fun w => s w = 0)).card := by
  classical
  have hswapT : ∀ w : ↥I, (z ∈ T ∧ z' ∈ T) → w ∈ T → Equiv.swap z z' w ∈ T := by
    intro w ⟨hzT, hz'T⟩ hwT
    rcases eq_or_ne w z with rfl | hwz
    · rwa [Equiv.swap_apply_left]
    · rcases eq_or_ne w z' with rfl | hwz'
      · rwa [Equiv.swap_apply_right]
      · rwa [Equiv.swap_apply_of_ne_of_ne hwz hwz']
  rcases h with hin | ⟨hz, hz'⟩
  · refine Finset.card_bij (fun w _ => Equiv.swap z z' w) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter] at hw ⊢
      exact ⟨hswapT w hin hw.1, hw.2⟩
    · intro w₁ _ w₂ _ heq; exact (Equiv.swap z z').injective heq
    · intro v hv
      simp only [Finset.mem_filter] at hv
      refine ⟨Equiv.swap z z' v, ?_, Equiv.swap_apply_self z z' v⟩
      simp only [Finset.mem_filter]
      exact ⟨hswapT v hin hv.1, by rw [Function.comp_apply, Equiv.swap_apply_self]; exact hv.2⟩
  · refine congrArg Finset.card (Finset.filter_congr (fun w hw => ?_))
    rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hz hw)
      (by rintro rfl; exact hz' hw)]

open scoped ComplexOrder in
/-- **The per-block weight states of a disconnected basis lie in the ground subspace**: for a cut
`(A, Aᶜ)` with no crossing μ-overlap, the fiber sum
`W_{p,q} = Σ_{s : upCount A = p, upCount Aᶜ = q} Slater(canonical I (extend s))` is a ground state.
Its coefficient `D(s) = [upCount A s = p][upCount Aᶜ s = q]` is edge-swap-invariant: a basis-graph
edge `z ~ z'` lies within one block (no crossing μ-overlap), so `swap z z'` preserves both block
up-counts (`upCountOn_comp_swap_eq`); membership follows from
`canonicalSlaterSum_mem_groundSubmodule_of_edgeSwap_invariant`. -/
theorem generalFlatBand_blockWeightState_mem_groundSubmodule
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)}
    {idx : Fin (M + 1) → Fin (M + 1)} (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    (A : Finset ↥I) (hcut : ∀ z ∈ A, ∀ w ∈ Aᶜ, ∀ x, μ z.1 x * μ w.1 x = 0) (p q : ℕ) :
    (∑ s : I → Fin 2, (if (A.filter (fun w => s w = 0)).card = p ∧
          (Aᶜ.filter (fun w => s w = 0)).card = q then (1 : ℂ) else 0) •
        generalFlatBandSlaterState μ
          (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)))
      ∈ generalFlatBandGroundSubmodule T U := by
  classical
  refine canonicalSlaterSum_mem_groundSubmodule_of_edgeSwap_invariant hbasis hT U hidx _
    (fun {z z'} hadj s => ?_)
  have hsame : (z ∈ A ∧ z' ∈ A) ∨ (z ∉ A ∧ z' ∉ A) := by
    obtain ⟨_, x, hzx, hz'x⟩ := hadj
    by_cases hzA : z ∈ A
    · by_cases hz'A : z' ∈ A
      · exact Or.inl ⟨hzA, hz'A⟩
      · exact absurd (hcut z hzA z' (Finset.mem_compl.mpr hz'A) x) (mul_ne_zero hzx hz'x)
    · by_cases hz'A : z' ∈ A
      · exact absurd (hcut z' hz'A z (Finset.mem_compl.mpr hzA) x) (mul_ne_zero hz'x hzx)
      · exact Or.inr ⟨hzA, hz'A⟩
  have hsameC : (z ∈ Aᶜ ∧ z' ∈ Aᶜ) ∨ (z ∉ Aᶜ ∧ z' ∉ Aᶜ) := by
    rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨fun hc => (Finset.mem_compl.mp hc) h1, fun hc => (Finset.mem_compl.mp hc) h2⟩
    · exact Or.inl ⟨Finset.mem_compl.mpr h1, Finset.mem_compl.mpr h2⟩
  rw [upCountOn_comp_swap_eq A s hsame, upCountOn_comp_swap_eq Aᶜ s hsameC]

/-- **A configuration with prescribed per-block up-counts exists**: for `p ≤ |A|`, `q ≤ |Aᶜ|`, some
`s : ↥I → Fin 2` has exactly `p` up-spins on `A` and `q` on `Aᶜ`.  Take `A₀ ⊆ A` of size `p` and
`B₀ ⊆ Aᶜ` of size `q`, set `s = 0` on `A₀ ∪ B₀` and `1` elsewhere. -/
theorem exists_blockUpCount_config {I : Finset (Fin (M + 1))} (A : Finset ↥I) {p q : ℕ}
    (hp : p ≤ A.card) (hq : q ≤ Aᶜ.card) :
    ∃ s : ↥I → Fin 2, (A.filter (fun z => s z = 0)).card = p ∧
      (Aᶜ.filter (fun z => s z = 0)).card = q := by
  classical
  obtain ⟨A₀, hA₀sub, hA₀c⟩ := Finset.exists_subset_card_eq hp
  obtain ⟨B₀, hB₀sub, hB₀c⟩ := Finset.exists_subset_card_eq hq
  refine ⟨fun z => if z ∈ A₀ ∪ B₀ then 0 else 1, ?_, ?_⟩
  · rw [show (A.filter (fun z => (if z ∈ A₀ ∪ B₀ then (0 : Fin 2) else 1) = 0)) = A₀ from ?_, hA₀c]
    ext z
    simp only [Finset.mem_filter]
    by_cases h : z ∈ A₀ ∪ B₀
    · rw [if_pos h, eq_self_iff_true, and_true]
      refine ⟨fun hzA => (Finset.mem_union.mp h).resolve_right (fun hzB =>
        absurd hzA (Finset.mem_compl.mp (hB₀sub hzB))), fun hz => hA₀sub hz⟩
    · rw [if_neg h]
      refine ⟨fun hzA => absurd hzA.2 (by decide), fun hz => ?_⟩
      exact absurd (Finset.mem_union.mpr (Or.inl hz)) h
  · rw [show (Aᶜ.filter (fun z => (if z ∈ A₀ ∪ B₀ then (0 : Fin 2) else 1) = 0)) = B₀ from ?_, hB₀c]
    ext z
    simp only [Finset.mem_filter]
    by_cases h : z ∈ A₀ ∪ B₀
    · rw [if_pos h, eq_self_iff_true, and_true]
      refine ⟨fun hzAc => (Finset.mem_union.mp h).resolve_left (fun hzA₀ =>
        absurd (hA₀sub hzA₀) (Finset.mem_compl.mp hzAc)), fun hz => hB₀sub hz⟩
    · rw [if_neg h]
      refine ⟨fun hzAc => absurd hzAc.2 (by decide), fun hz => ?_⟩
      exact absurd (Finset.mem_union.mpr (Or.inr hz)) h

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

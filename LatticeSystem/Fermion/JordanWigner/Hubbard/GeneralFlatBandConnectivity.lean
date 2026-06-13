import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandTwoHoleCollapse

/-!
# Flat-band ground-state connectivity induction (Tasaki §11.3.4, eq. (11.3.49))

The eq. (11.3.49) Marshall-sign relation `D(σ) = D(σ_{a↔b})` for a connected pair, and its
promotion through the special-basis connectivity graph to: on a *connected* basis the ground-state
coefficient `D` depends only on the up-count, whence the ground subspace has `finrank ≤ D₀ + 1`.

Built on the single-term collapse and Koszul sign flip of `GeneralFlatBandTwoHoleCollapse.lean`
(`cDownUp_canonicalSum_eq_two_terms`, `cDownUp_canonical_repr_twoHole_swap_eq_neg`).  Edge-swap
invariance is lifted along graph walks (path conjugation) and, for a connected graph, to all of
`Perm I` (transpositions generate), giving the up-count dependence and the dimension bound.

Split from `GeneralFlatBandTwoHoleCollapse.lean` (build-speed refactor, 20-PR cadence).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.49).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators ComplexOrder

variable {M : ℕ}

/-- **The eq. (11.3.49) Marshall-sign relation**: for a flat-band ground state `Φ` with spin-config
expansion `Φ = Σ_s D s • Slater(canonical I (extend s))`, and a connected pair `a, b ∈ I` (i.e. a
site `x` with `μ_a(x) ≠ 0` and `μ_b(x) ≠ 0`) with `σ a = 0`, `σ b = 1`, the coefficient of `σ|_I`
equals that of the `a↔b` spin-swapped config `(σ ∘ swap a b)|_I`.  Acting with `ĉ_{x,↓}ĉ_{x,↑}`
kills the ground state (`generalCDownUp_mulVec_eq_zero_of_mem_groundSubmodule`); taking the
`(a,b)`-emptied coordinate, the sum collapses (`cDownUp_canonicalSum_eq_two_terms`) to the two
relevant configs, whose coordinates are negatives (`cDownUp_canonical_repr_twoHole_swap_eq_neg`) and
nonzero (the `μ`-amplitudes and the rest coordinate are nonzero), forcing `D σ = D σ_{a↔b}`. -/
theorem flatBand_groundState_D_swap_eq {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) {a b : Fin (M + 1)} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b)
    (hσa : σ a = 0) (hσb : σ b = 1) (hμa : μ a x ≠ 0) (hμb : μ b x ≠ 0)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (D : (I → Fin 2) → ℂ)
    (hD : Φ = ∑ s, D s • generalFlatBandSlaterState μ
      (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))) :
    D (fun z : I => σ z.1) = D (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1) := by
  set g := idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ) with hg
  -- coord_σ ≠ 0
  have hcoordne : (generalOccBasis eμ).repr ((generalCDownUp M x).mulVec
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ))) g ≠ 0 := by
    rw [cDownUp_canonical_repr_twoHole hbasis hidx σ x ha hb hab hσa hσb]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero hμa
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero hμb ?_)))
    exact generalFlatBandSlaterState_repr_self_ne_zero hbasis eμ idx hidx _
      (flatBandSpinConfigList_nodup _ _)
      (fun q hq => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
        (flatBandSpinConfigList_mem_fst_mem _ σ hq)))
  -- cDownUp Φ = 0 → coordinate sum = 0
  have hzero := generalCDownUp_mulVec_eq_zero_of_mem_groundSubmodule T U hT hU hΦ x
  have h0 : (generalOccBasis eμ).repr ((generalCDownUp M x).mulVec Φ) g = 0 := by rw [hzero]; simp
  rw [hD, Matrix.mulVec_sum] at h0
  simp only [Matrix.mulVec_smul, map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  rw [cDownUp_canonicalSum_eq_two_terms hbasis hidx σ x ha hb hab hσa hσb D] at h0
  have hc0 : flatBandSpinConfigList I
        (fun z => if h : z ∈ I then (fun z : I => σ z.1) ⟨z, h⟩ else 0)
      = flatBandSpinConfigList I σ := by
    apply flatBandSpinConfigList_congr; intro z hz; simp only [hz, dif_pos]
  have hc0' : flatBandSpinConfigList I
        (fun z => if h : z ∈ I then (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1) ⟨z, h⟩ else 0)
      = flatBandSpinConfigList I (σ ∘ ⇑(Equiv.swap a b)) := by
    apply flatBandSpinConfigList_congr; intro z hz; simp only [hz, dif_pos]
  rw [hc0, hc0'] at h0
  have hpr55 := cDownUp_canonical_repr_twoHole_swap_eq_neg hbasis hidx σ x ha hb hab hσa hσb
  rw [hpr55] at h0
  set csw := (generalOccBasis eμ).repr ((generalCDownUp M x).mulVec
    (generalFlatBandSlaterState μ (flatBandSpinConfigList I (σ ∘ ⇑(Equiv.swap a b))))) g with hcsw
  have hcswne : csw ≠ 0 := fun hc => hcoordne (by rw [hpr55, hc, neg_zero])
  have hfin : (D (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1)
      - D (fun z : I => σ z.1)) * csw = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp hfin with h | h
  · exact (sub_eq_zero.mp h).symm
  · exact absurd h hcswne

/-- **Graph-adjacent indices give equal ground-state coefficients** (eq. (11.3.49) on the
special-basis graph): if `z, z'` are adjacent in the special-basis connectivity graph (so
`∃ x, μ_z(x) ≠ 0` and
`μ_{z'}(x) ≠ 0`) and `σ z = 0`, `σ z' = 1`, then the coefficient of `σ|_I` equals that of the
`z↔z'` spin-swapped config.  Extracts the witnessing site `x` from the adjacency and applies
`flatBand_groundState_D_swap_eq`.  This is the per-edge step of the connectivity induction. -/
theorem flatBand_groundState_D_swap_eq_of_adj {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (D : (I → Fin 2) → ℂ)
    (hD : Φ = ∑ s, D s • generalFlatBandSlaterState μ
      (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)))
    {z z' : I} (hadj : (generalFlatBandBasisGraph I μ).Adj z z')
    (hσz : σ z.1 = 0) (hσz' : σ z'.1 = 1) :
    D (fun w : I => σ w.1) = D (fun w : I => (σ ∘ ⇑(Equiv.swap z.1 z'.1)) w.1) := by
  obtain ⟨hne, x, hμz, hμz'⟩ := hadj
  exact flatBand_groundState_D_swap_eq hbasis hT U hU hidx σ x z.2 z'.2 hne hσz hσz'
    hμz hμz' hΦ D hD

/-- **Unconditional edge-swap invariance of the ground-state coefficients**: for `z, z'` adjacent in
the special-basis connectivity graph, `D σ = D (σ ∘ swap z z')` with *no* spin condition.  When
`σ z = σ z'` the swap leaves the config unchanged; otherwise one of `z, z'` is `↑` and the other
`↓`, and `flatBand_groundState_D_swap_eq_of_adj` (the eq. (11.3.49) per-edge relation) applies in
the appropriate orientation.  Hence `D` is invariant under every edge-transposition of the basis
graph, the input to the connectivity-induction "D depends only on the up-count". -/
theorem flatBand_groundState_D_edgeSwap_eq {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (D : (I → Fin 2) → ℂ)
    (hD : Φ = ∑ s, D s • generalFlatBandSlaterState μ
      (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)))
    {z z' : I} (hadj : (generalFlatBandBasisGraph I μ).Adj z z') :
    D (fun w : I => σ w.1) = D (fun w : I => (σ ∘ ⇑(Equiv.swap z.1 z'.1)) w.1) := by
  have hne : z.1 ≠ z'.1 := hadj.1
  by_cases hsame : σ z.1 = σ z'.1
  · -- σ∘swap = σ ⟹ D args equal
    have : (fun w : I => σ w.1) = (fun w : I => (σ ∘ ⇑(Equiv.swap z.1 z'.1)) w.1) := by
      funext w
      simp only [Function.comp]
      by_cases hw : w.1 = z.1
      · rw [hw, Equiv.swap_apply_left, hsame]
      · by_cases hw' : w.1 = z'.1
        · rw [hw', Equiv.swap_apply_right, hsame]
        · rw [Equiv.swap_apply_of_ne_of_ne hw hw']
    rw [this]
  · -- one up one down
    rcases fin2_eq_zero_or_one (σ z.1) with h0 | h1
    · have h1' : σ z'.1 = 1 := by
        rcases fin2_eq_zero_or_one (σ z'.1) with hh | hh
        · exact absurd (h0.trans hh.symm) hsame
        · exact hh
      exact flatBand_groundState_D_swap_eq_of_adj hbasis hT U hU hidx σ hΦ D hD hadj h0 h1'
    · have h0' : σ z'.1 = 0 := by
        rcases fin2_eq_zero_or_one (σ z'.1) with hh | hh
        · exact hh
        · exact absurd (h1.trans hh.symm) hsame
      have := flatBand_groundState_D_swap_eq_of_adj hbasis hT U hU hidx σ hΦ D hD hadj.symm h0' h1
      rw [Equiv.swap_comm] at this
      exact this

/-- **Edge-swap invariance as an `Equiv.Perm I` action**: for `z, z'` adjacent in the special-basis
graph, `D s = D (s ∘ Equiv.swap z z')` for every config `s : I → Fin 2`.  Extending `s` to a full
`σ` and applying `flatBand_groundState_D_edgeSwap_eq`, the restricted swapped config is exactly
`s ∘ Equiv.swap z z'`.  This is the per-generator step for the symmetric-group action: `D` is
invariant under every edge-transposition of the basis graph, viewed as a permutation of `I`. -/
theorem flatBand_groundState_D_permSwap_eq {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (D : (I → Fin 2) → ℂ)
    (hD : Φ = ∑ s, D s • generalFlatBandSlaterState μ
      (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)))
    (s : I → Fin 2) {z z' : I} (hadj : (generalFlatBandBasisGraph I μ).Adj z z') :
    D s = D (s ∘ ⇑(Equiv.swap z z')) := by
  set σ := fun w => if h : w ∈ I then s ⟨w, h⟩ else (0 : Fin 2) with hσdef
  have hsσ : (fun w : I => σ w.1) = s := by funext w; simp only [hσdef, w.2, dif_pos]
  have hkey := flatBand_groundState_D_edgeSwap_eq hbasis hT U hU hidx σ hΦ D hD hadj
  rw [hsσ] at hkey
  rw [hkey]
  congr 1
  funext w
  simp only [Function.comp, hσdef]
  by_cases hwz : w = z
  · subst hwz; rw [Equiv.swap_apply_left, Equiv.swap_apply_left, dif_pos z'.2]
  · by_cases hwz' : w = z'
    · subst hwz'; rw [Equiv.swap_apply_right, Equiv.swap_apply_right, dif_pos z.2]
    · rw [Equiv.swap_apply_of_ne_of_ne hwz hwz',
        Equiv.swap_apply_of_ne_of_ne (fun h => hwz (Subtype.ext h)) (fun h => hwz' (Subtype.ext h)),
        dif_pos w.2]

/-- **Walk-swap invariance**: for a walk `z ⤳ z'` in the special-basis connectivity graph,
`D (s ∘ Equiv.swap z z') = D s`.  Induction on the walk: the empty walk gives the identity swap; a
`cons` step decomposes `Equiv.swap z z'` as the conjugate `Equiv.swap z w * Equiv.swap w z' *
Equiv.swap z w` (when `z' ∉ {z, w}`), each factor invariant (the edge by
`flatBand_groundState_D_permSwap_eq`, the tail by induction), and `D`-invariance is closed under
products.  Hence reachable indices give equal coefficients after swapping. -/
theorem flatBand_groundState_D_swap_eq_of_walk {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (D : (I → Fin 2) → ℂ)
    (hD : Φ = ∑ s, D s • generalFlatBandSlaterState μ
      (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))) :
    ∀ {z z' : I}, (generalFlatBandBasisGraph I μ).Walk z z' →
      ∀ s : I → Fin 2, D (s ∘ ⇑(Equiv.swap z z')) = D s := by
  have hmul : ∀ {π π' : Equiv.Perm I}, (∀ s, D (s ∘ π) = D s) → (∀ s, D (s ∘ π') = D s) →
      ∀ s, D (s ∘ (π * π')) = D s := by
    intro π π' hπ hπ' s
    have : s ∘ ⇑(π * π') = (s ∘ ⇑π) ∘ ⇑π' := by funext x; simp [Equiv.Perm.coe_mul]
    rw [this, hπ', hπ]
  intro z z' w
  induction w with
  | nil => intro s; simp [Equiv.swap_self]
  | @cons u v z' hadj p ih =>
    intro s
    have hedge : ∀ s, D (s ∘ ⇑(Equiv.swap u v)) = D s :=
      fun s => (flatBand_groundState_D_permSwap_eq hbasis hT U hU hidx hΦ D hD s hadj).symm
    by_cases hz'u : z' = u
    · subst hz'u; simp [Equiv.swap_self]
    · by_cases hz'v : z' = v
      · subst hz'v; exact hedge s
      · have hconj : Equiv.swap u z' = Equiv.swap u v * Equiv.swap v z' * Equiv.swap u v := by
          have h := Equiv.swap_apply_apply (Equiv.swap u v) v z'
          rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hz'u hz'v,
            Equiv.swap_inv] at h
          exact h
        rw [hconj]
        exact hmul hedge (hmul ih hedge) s

/-- **Permutation invariance of the ground-state coefficients on a connected basis**: if the
special basis is connected, then `D (s ∘ π) = D s` for *every* permutation `π : Equiv.Perm I`.  The
set of `D`-invariant permutations is a subgroup containing every transposition (each
`Equiv.swap a b` is invariant via a walk between `a` and `b`, which connectivity supplies); since
transpositions generate the whole symmetric group (`Equiv.Perm.closure_isSwap`), that subgroup is
`⊤`. -/
theorem flatBand_groundState_D_perm_eq {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (D : (I → Fin 2) → ℂ)
    (hD : Φ = ∑ s, D s • generalFlatBandSlaterState μ
      (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)))
    (hconn : generalFlatBandBasisConnected I μ) (π : Equiv.Perm I) (s : I → Fin 2) :
    D (s ∘ ⇑π) = D s := by
  -- D-invariance subgroup
  let G : Subgroup (Equiv.Perm I) :=
    { carrier := {ρ | ∀ t : I → Fin 2, D (t ∘ ⇑ρ) = D t}
      one_mem' := by intro t; simp
      mul_mem' := by
        intro ρ ρ' hρ hρ' t
        have : t ∘ ⇑(ρ * ρ') = (t ∘ ⇑ρ) ∘ ⇑ρ' := by funext x; simp [Equiv.Perm.coe_mul]
        rw [this, hρ', hρ]
      inv_mem' := by
        intro ρ hρ t
        have h := hρ (t ∘ ⇑ρ⁻¹)
        have he : (t ∘ ⇑ρ⁻¹) ∘ ⇑ρ = t := by funext x; simp
        rw [he] at h; exact h.symm }
  have hswap : ∀ ρ : Equiv.Perm I, ρ.IsSwap → ρ ∈ G := by
    rintro ρ ⟨a, b, hab, rfl⟩
    intro t
    have hreach : (generalFlatBandBasisGraph I μ).Reachable a b :=
      (hconn.preconnected a b)
    obtain ⟨w⟩ := hreach
    exact flatBand_groundState_D_swap_eq_of_walk hbasis hT U hU hidx hΦ D hD w t
  have htop : G = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← Equiv.Perm.closure_isSwap]
    exact (Subgroup.closure_le G).mpr hswap
  have hπ : π ∈ G := by rw [htop]; exact Subgroup.mem_top π
  exact hπ s

/-- **The ground-state coefficient depends only on the up-count** (connected basis): if `s, s'` have
the same number of up-spins (`Fintype.card {z // s z = 0} = Fintype.card {z // s' z = 0}`), then
`D s = D s'`.  Equal-weight configs differ by a permutation (`exists_perm_comp_of_card_eq`), under
which `D` is invariant on a connected basis (`flatBand_groundState_D_perm_eq`). -/
theorem flatBand_groundState_D_const_of_weight_eq {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (D : (I → Fin 2) → ℂ)
    (hD : Φ = ∑ s, D s • generalFlatBandSlaterState μ
      (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)))
    (hconn : generalFlatBandBasisConnected I μ) (s s' : I → Fin 2)
    (hw : Fintype.card {z // s z = 0} = Fintype.card {z // s' z = 0}) :
    D s = D s' := by
  obtain ⟨π, hπ⟩ := exists_perm_comp_of_card_eq s s' hw
  rw [← hπ, flatBand_groundState_D_perm_eq hbasis hT U hU hidx hΦ D hD hconn]

/-- **Ground-subspace dimension upper bound on a connected basis** (Tasaki §11.3.4, toward the
`(D₀+1)`-fold multiplet): on a connected special basis, the flat-band ground subspace has
`finrank ≤ D₀ + 1`.  Every ground state decomposes into `μ`-Slater states
(`flatBand_groundState_eq_canonicalSlaterSum`) whose coefficient depends only on the up-count
(`flatBand_groundState_D_const_of_weight_eq`); grouping the decomposition by up-count
(`Finset.sum_fiberwise_of_maps_to`) and factoring the constant coefficient out of each fiber, every
ground state lies in the span of the `D₀ + 1` symmetric weight-states `W_0, …, W_{D₀}`. -/
theorem generalFlatBandGround_finrank_le_of_connected
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    (hconn : generalFlatBandBasisConnected I μ) :
    Module.finrank ℂ (generalFlatBandGroundSubmodule T U) ≤ generalFlatBandDim T + 1 := by
  classical
  set E := (Fin (2 * M + 2) → Fin 2) → ℂ
  let W : ℕ → E := fun k => ∑ s ∈ (Finset.univ.filter (fun s : I → Fin 2 =>
    Fintype.card {z // s z = 0} = k)), generalFlatBandSlaterState μ
      (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))
  let S : Finset E := (Finset.range (I.card + 1)).image W
  let K : Submodule ℂ E := Submodule.span ℂ (S : Set E)
  have hcover : generalFlatBandGroundSubmodule T U ≤ K := by
    intro Φ hΦ
    obtain ⟨D, hD⟩ := flatBand_groundState_eq_canonicalSlaterSum hbasis hT U hU eμ idx hidx hΦ
    rw [hD]
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun s : I → Fin 2 => Fintype.card {z // s z = 0}) (s := Finset.univ)
      (t := Finset.range (I.card + 1))
      (f := fun s => D s • generalFlatBandSlaterState μ
        (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)))
      (fun s _ => Finset.mem_range.mpr (Nat.lt_succ_of_le
        ((Fintype.card_subtype_le (fun z : I => s z = 0)).trans_eq (Fintype.card_coe I))))]
    refine Submodule.sum_mem K ?_
    intro k hk
    rcases (Finset.univ.filter
        (fun s : I → Fin 2 => Fintype.card {z // s z = 0} = k)).eq_empty_or_nonempty
      with he | ⟨s0, hs0⟩
    · rw [he, Finset.sum_empty]; exact Submodule.zero_mem K
    · have hfac : (∑ s ∈ Finset.univ.filter (fun s : I → Fin 2 => Fintype.card {z // s z = 0} = k),
          D s • generalFlatBandSlaterState μ
            (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)))
          = D s0 • W k := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun s hs => ?_)
        have hws : Fintype.card {z // s z = 0} = Fintype.card {z // s0 z = 0} := by
          rw [(Finset.mem_filter.mp hs).2, (Finset.mem_filter.mp hs0).2]
        rw [flatBand_groundState_D_const_of_weight_eq hbasis hT U hU hidx hΦ D hD hconn s s0 hws]
      rw [hfac]
      exact Submodule.smul_mem K (D s0) (Submodule.subset_span (Finset.mem_image_of_mem W hk))
  calc Module.finrank ℂ (generalFlatBandGroundSubmodule T U)
      ≤ Module.finrank ℂ K := Submodule.finrank_mono hcover
    _ ≤ S.card := finrank_span_finset_le_card S
    _ ≤ (Finset.range (I.card + 1)).card := Finset.card_image_le
    _ = I.card + 1 := Finset.card_range _
    _ = generalFlatBandDim T + 1 := by rw [hbasis.1]

end LatticeSystem.Fermion

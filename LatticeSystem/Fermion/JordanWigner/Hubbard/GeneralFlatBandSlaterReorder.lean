import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandSignPropagation

/-!
# Slater reordering and the cDownUp pair extraction (Tasaki §11.3.4, eqs. 11.3.48/49)

The combinatorial machinery for the eq. (11.3.48) double-annihilation sign relation: permutation
scaling of `μ`-Slater states, the canonical (sorted) spin-config creation list, the head/two-head
site-annihilation extraction, the move-a-pair-to-the-front reordering, the per-pair extraction at an
arbitrary position (with the canonical/swap relative `−1`), and the order-fixed canonical-Slater
`D`-coefficient expansion of a flat-band ground state.

Split from `GeneralFlatBandSignPropagation.lean` (the eq. (11.3.48) coefficient setup) for build
speed.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eqs. (11.3.48)–(11.3.49).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators ComplexOrder

variable {M : ℕ}

/-- Swapping the first two creations of a `μ`-Slater state negates it (the two leading `â†` factors
anticommute).  The `generalFlatBandSlaterState` analogue of `generalModeMonomial_swap`. -/
theorem generalFlatBandSlaterState_swap (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (x y : Fin (M + 1) × Fin 2) (l : List (Fin (M + 1) × Fin 2)) :
    generalFlatBandSlaterState μ (y :: x :: l) = -generalFlatBandSlaterState μ (x :: y :: l) := by
  unfold generalFlatBandSlaterState
  simp only [List.map_cons, List.prod_cons, generalFlatBandCreation]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    eq_neg_of_add_eq_zero_left
      (spinfulFromVector_creation_creation_anticomm M (μ y.1) (μ x.1) y.2 x.2),
    Matrix.neg_mul, Matrix.neg_mulVec]

/-- **Reordering a `μ`-Slater state scales it by a nonzero sign**: a permutation of the creation
list multiplies the Slater state by a nonzero (`±1`) scalar.  The `generalFlatBandSlaterState`
analogue of `generalModeMonomial_perm`; lets list orderings (e.g. the opaque preimage list vs. a
canonical order) be compared up to a tracked sign. -/
theorem generalFlatBandSlaterState_perm (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    {l l' : List (Fin (M + 1) × Fin 2)} (h : l.Perm l') :
    ∃ z : ℂ, z ≠ 0 ∧ generalFlatBandSlaterState μ l = z • generalFlatBandSlaterState μ l' := by
  induction h with
  | nil => exact ⟨1, one_ne_zero, by rw [one_smul]⟩
  | cons x _ ih =>
    obtain ⟨z, hz0, hz⟩ := ih
    refine ⟨z, hz0, ?_⟩
    rw [← generalFlatBandCreation_mulVec_slaterState, hz, Matrix.mulVec_smul,
      generalFlatBandCreation_mulVec_slaterState]
  | swap x y l =>
    exact ⟨-1, neg_ne_zero.mpr one_ne_zero, by rw [generalFlatBandSlaterState_swap, neg_one_smul]⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨z₁, hz₁0, hz₁⟩ := ih₁
    obtain ⟨z₂, hz₂0, hz₂⟩ := ih₂
    exact ⟨z₁ * z₂, mul_ne_zero hz₁0 hz₂0, by rw [hz₁, hz₂, smul_smul]⟩

/-- **The occupied finset of a spin-configuration occupation** is `{(idx z, σ z) : z ∈ I}`. -/
theorem flatBandSpinConfigOcc_occFinset (I : Finset (Fin (M + 1)))
    (idx : Fin (M + 1) → Fin (M + 1)) (σ : Fin (M + 1) → Fin 2) :
    generalOccFinset (flatBandSpinConfigOcc I idx σ) = I.image (fun z => (idx z, σ z)) := by
  ext q
  simp only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    flatBandSpinConfigOcc]
  by_cases h : ∃ z ∈ I, q = (idx z, σ z)
  · obtain ⟨z, hz, rfl⟩ := h
    exact iff_of_true (if_pos ⟨z, hz, rfl⟩) ⟨z, hz, rfl⟩
  · rw [if_neg h]
    exact iff_of_false (by decide) (fun ⟨z, hz, hzq⟩ => h ⟨z, hz, hzq.symm⟩)

/-- **The canonical (sorted) creation list of a spin configuration**: `(z, σ z)` for `z ∈ I` in
increasing order of `z`.  The orbital-ordered list on which the eq. (11.3.48) double-annihilation
acts with explicit positions and Koszul signs (the general-basis analogue of the Theorem 11.11
`flatBandAlphaSpinList`). -/
def flatBandSpinConfigList (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2) :
    List (Fin (M + 1) × Fin 2) :=
  (I.sort (· ≤ ·)).map (fun z => (z, σ z))

/-- The canonical list is nodup. -/
theorem flatBandSpinConfigList_nodup (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2) :
    (flatBandSpinConfigList I σ).Nodup :=
  (I.sort_nodup _).map fun _ _ hab => (Prod.ext_iff.mp hab).1

/-- The canonical list enumerates the occupied modes `{(z, σ z) : z ∈ I}` of `σ`. -/
theorem flatBandSpinConfigList_toFinset (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2) :
    (flatBandSpinConfigList I σ).toFinset = I.image (fun z => (z, σ z)) := by
  ext q
  simp only [flatBandSpinConfigList, List.mem_toFinset, List.mem_map, Finset.mem_sort,
    Finset.mem_image]

/-- **The canonical list is a permutation of the `μ`-Slater preimage list** of the spin
configuration: both enumerate `{(z, σ z) : z ∈ I}` without repetition. -/
theorem flatBandSpinConfigList_perm_preimageList {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2) :
    (flatBandSpinConfigList I σ).Perm
      (flatBandSpecialPreimageList I idx (flatBandSpinConfigOcc I idx σ)) := by
  classical
  refine List.perm_of_nodup_nodup_toFinset_eq (flatBandSpinConfigList_nodup I σ) ?_ ?_
  · rw [flatBandSpecialPreimageList]
    refine ((generalOccFinset _).nodup_toList).map_on fun a ha b hb hab => ?_
    have hga : flatBandSpinConfigOcc I idx σ a = 1 := by
      have := Finset.mem_toList.mp ha
      simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have hgb : flatBandSpinConfigOcc I idx σ b = 1 := by
      have := Finset.mem_toList.mp hb
      simpa only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have ha1 : idx (flatBandSpecialIdxInv I idx a.1) = a.1 := idx_flatBandSpecialIdxInv
      (Finset.mem_image.mp (flatBandSpinConfigOcc_idxSupported I idx σ a hga))
    have hb1 : idx (flatBandSpecialIdxInv I idx b.1) = b.1 := idx_flatBandSpecialIdxInv
      (Finset.mem_image.mp (flatBandSpinConfigOcc_idxSupported I idx σ b hgb))
    have hab1 : flatBandSpecialIdxInv I idx a.1 = flatBandSpecialIdxInv I idx b.1 :=
      (Prod.ext_iff.mp hab).1
    exact Prod.ext (by rw [← ha1, hab1, hb1]) (Prod.ext_iff.mp hab).2
  · rw [flatBandSpinConfigList_toFinset]
    ext q'
    constructor
    · intro hq'
      rw [Finset.mem_image] at hq'
      obtain ⟨z, hz, rfl⟩ := hq'
      rw [List.mem_toFinset, flatBandSpecialPreimageList, List.mem_map]
      refine ⟨(idx z, σ z), ?_, ?_⟩
      · rw [Finset.mem_toList, flatBandSpinConfigOcc_occFinset, Finset.mem_image]
        exact ⟨z, hz, rfl⟩
      · rw [flatBandSpecialIdxInv_idx hbasis hidx hz]
    · intro hq'
      rw [List.mem_toFinset, flatBandSpecialPreimageList, List.mem_map] at hq'
      obtain ⟨q, hq, rfl⟩ := hq'
      rw [Finset.mem_toList, flatBandSpinConfigOcc_occFinset, Finset.mem_image] at hq
      obtain ⟨z, hz, rfl⟩ := hq
      rw [Finset.mem_image]
      exact ⟨z, hz, by rw [flatBandSpecialIdxInv_idx hbasis hidx hz]⟩

/-- **The spin-configuration state is a nonzero scalar multiple of its canonical-list Slater
state**: `flatBandSpinConfigState σ = z·generalFlatBandSlaterState μ (flatBandSpinConfigList σ)` for
a nonzero sign `z`.  This puts the state in the orbital-ordered form on which the eq. (11.3.48)
double peel has explicit positions and signs.  From the preimage-list Slater form (PR13) and the
permutation scaling (PR16). -/
theorem flatBandSpinConfigState_eq_smul_canonical {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2) :
    ∃ z : ℂ, z ≠ 0 ∧ flatBandSpinConfigState I idx eμ σ
      = z • generalFlatBandSlaterState μ (flatBandSpinConfigList I σ) := by
  rw [flatBandSpinConfigState_eq_slaterState hidx]
  exact generalFlatBandSlaterState_perm μ
    (flatBandSpinConfigList_perm_preimageList hbasis hidx σ).symm

/-- **Site annihilation extracts the leading matching-spin head**: if `rest` carries no
matching-spin connected mode at `x`, then `ĉ_{x,σ}` removes the leading creation `(z, σ)` with
amplitude `μ_z(x)`, leaving the Slater state of `rest`.  (General-basis analogue of the Theorem
11.11 `flatBand_siteAnnihilation_head`.) -/
theorem generalFlatBand_siteAnnihilation_head (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (x z : Fin (M + 1)) (σ : Fin 2) (rest : List (Fin (M + 1) × Fin 2))
    (hrest : ∀ q ∈ rest, μ q.1 x = 0 ∨ q.2 ≠ σ) :
    (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)).mulVec
        (generalFlatBandSlaterState μ ((z, σ) :: rest))
      = μ z x • generalFlatBandSlaterState μ rest := by
  rw [generalFlatBand_siteAnnihilation_peel]
  change ∑ i : Fin (rest.length + 1), generalFlatBandPeelTerm μ x σ ((z, σ) :: rest) i = _
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => ?_), add_zero]
  · simp only [generalFlatBandPeelTerm, List.get_cons_zero, List.eraseIdx_cons_zero, Fin.val_zero,
      pow_zero, one_smul]
    rw [if_true]
  · simp only [generalFlatBandPeelTerm, List.get_cons_succ', List.eraseIdx_cons_succ, Fin.val_succ]
    rcases hrest (rest.get i) (List.get_mem rest i) with h0 | hne
    · rw [h0, ite_self]; simp
    · rw [if_neg hne]; simp

/-- **The double annihilation extracts the leading up–down head pair**: if `rest` is disconnected
from `x` (`μ_{q.1}(x) = 0`), then `ĉ_{x,↓}ĉ_{x,↑}` removes the leading up head `(a, ↑)` and down
head `(b, ↓)`, leaving `μ_a(x)·μ_b(x)·Slater(rest)`.  (General-basis analogue of the Theorem 11.11
`flatBand_cDownUp_two_head`; the seed of the eq. (11.3.48) sign relation.) -/
theorem generalFlatBand_cDownUp_two_head (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (x a b : Fin (M + 1)) (rest : List (Fin (M + 1) × Fin 2))
    (hrest : ∀ q ∈ rest, μ q.1 x = 0) :
    (generalCDownUp M x).mulVec
        (generalFlatBandSlaterState μ ((a, (0 : Fin 2)) :: (b, (1 : Fin 2)) :: rest))
      = (μ a x * μ b x) • generalFlatBandSlaterState μ rest := by
  rw [generalCDownUp, ← Matrix.mulVec_mulVec,
    generalFlatBand_siteAnnihilation_head μ x a 0 ((b, (1 : Fin 2)) :: rest)
      (fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact Or.inr (show (1 : Fin 2) ≠ 0 by decide)
        · exact Or.inl (hrest q hq')),
    Matrix.mulVec_smul,
    generalFlatBand_siteAnnihilation_head μ x b 1 rest (fun q hq => Or.inl (hrest q hq)), smul_smul]

/-- **The double annihilation on a swapped down–up head pair**: if `rest` is disconnected from `x`,
then `ĉ_{x,↓}ĉ_{x,↑}` on `(a, ↓) :: (b, ↑) :: rest` gives `−μ_a(x)·μ_b(x)·Slater(rest)` — the
**opposite sign** from the canonical up–down assignment (one extra Koszul transposition).  This
relative `−1` is exactly the seed of the eq. (11.3.49) sign relation `C(σ) = C(σ_{z₁↔z₂})`
(general-basis analogue of the Theorem 11.11 `flatBand_cDownUp_swap`). -/
theorem generalFlatBand_cDownUp_two_head_swap (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (x a b : Fin (M + 1)) (rest : List (Fin (M + 1) × Fin 2))
    (hrest : ∀ q ∈ rest, μ q.1 x = 0) :
    (generalCDownUp M x).mulVec
        (generalFlatBandSlaterState μ ((a, (1 : Fin 2)) :: (b, (0 : Fin 2)) :: rest))
      = (-(μ a x * μ b x)) • generalFlatBandSlaterState μ rest := by
  rw [generalFlatBandSlaterState_swap μ (b, 0) (a, 1) rest, Matrix.mulVec_neg,
    generalFlatBand_cDownUp_two_head μ x b a rest hrest, ← neg_smul]
  congr 1
  ring

/-- Moving the head `c` past the next two creations `a, b` preserves the Slater state (sign `+1`:
two adjacent transpositions).  General-basis analogue of
`flatBandModeMonomial_move_one_past_two`. -/
theorem generalFlatBandSlaterState_move_one_past_two (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (c a b : Fin (M + 1) × Fin 2) (l : List (Fin (M + 1) × Fin 2)) :
    generalFlatBandSlaterState μ (c :: a :: b :: l)
      = generalFlatBandSlaterState μ (a :: b :: c :: l) := by
  rw [generalFlatBandSlaterState_swap μ a c (b :: l),
    ← generalFlatBandCreation_mulVec_slaterState μ a.1 a.2,
    generalFlatBandSlaterState_swap μ b c l, Matrix.mulVec_neg,
    generalFlatBandCreation_mulVec_slaterState μ a.1 a.2, neg_neg]

/-- **Moving a contiguous pair to the front of a Slater state preserves it** (sign `+1`): pushing
the pair `a, b` leftward past the block `l₁` is `2·|l₁|` adjacent transpositions, hence
`Slater(l₁ ++ a :: b :: l₂) = Slater(a :: b :: (l₁ ++ l₂))`.  General-basis analogue of
`flatBandModeMonomial_move_pair_front`; brings an arbitrary occupied pair to the head for the
`cDownUp` two-head extraction. -/
theorem generalFlatBandSlaterState_move_pair_front (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (a b : Fin (M + 1) × Fin 2) (l₁ l₂ : List (Fin (M + 1) × Fin 2)) :
    generalFlatBandSlaterState μ (l₁ ++ a :: b :: l₂)
      = generalFlatBandSlaterState μ (a :: b :: (l₁ ++ l₂)) := by
  induction l₁ with
  | nil => rfl
  | cons c l₁' ih =>
    rw [List.cons_append, ← generalFlatBandCreation_mulVec_slaterState μ c.1 c.2, ih,
      generalFlatBandCreation_mulVec_slaterState μ c.1 c.2,
      generalFlatBandSlaterState_move_one_past_two μ c a b (l₁' ++ l₂), List.cons_append]

/-- **Extracting an up–down pair at an arbitrary position**: if the surrounding blocks `l₁, l₂` are
disconnected from `x`, then `ĉ_{x,↓}ĉ_{x,↑}` on `l₁ ++ (a,↑) :: (b,↓) :: l₂` removes the pair
`(a,↑), (b,↓)` with amplitude `μ_a(x)·μ_b(x)`, leaving `Slater(l₁ ++ l₂)`.  (Move the pair to the
head, then
the two-head extraction — the per-pair contribution of eq. (11.3.48) for a canonical up–down
assignment.) -/
theorem generalFlatBand_cDownUp_extract_pair (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (x a b : Fin (M + 1)) (l₁ l₂ : List (Fin (M + 1) × Fin 2))
    (h1 : ∀ q ∈ l₁, μ q.1 x = 0) (h2 : ∀ q ∈ l₂, μ q.1 x = 0) :
    (generalCDownUp M x).mulVec
        (generalFlatBandSlaterState μ (l₁ ++ (a, (0 : Fin 2)) :: (b, (1 : Fin 2)) :: l₂))
      = (μ a x * μ b x) • generalFlatBandSlaterState μ (l₁ ++ l₂) := by
  rw [generalFlatBandSlaterState_move_pair_front,
    generalFlatBand_cDownUp_two_head μ x a b (l₁ ++ l₂)
      (fun q hq => (List.mem_append.mp hq).elim (h1 q) (h2 q))]

/-- **Extracting a swapped down–up pair at an arbitrary position**: the swapped assignment `(a,↓),
(b,↑)` extracts with the **opposite** sign `−μ_a(x)·μ_b(x)`, leaving `Slater(l₁ ++ l₂)`.  This
relative `−1` between the two spin assignments of the same index pair is the per-pair eq. (11.3.49)
sign relation. -/
theorem generalFlatBand_cDownUp_extract_pair_swap (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (x a b : Fin (M + 1)) (l₁ l₂ : List (Fin (M + 1) × Fin 2))
    (h1 : ∀ q ∈ l₁, μ q.1 x = 0) (h2 : ∀ q ∈ l₂, μ q.1 x = 0) :
    (generalCDownUp M x).mulVec
        (generalFlatBandSlaterState μ (l₁ ++ (a, (1 : Fin 2)) :: (b, (0 : Fin 2)) :: l₂))
      = (-(μ a x * μ b x)) • generalFlatBandSlaterState μ (l₁ ++ l₂) := by
  rw [generalFlatBandSlaterState_move_pair_front,
    generalFlatBand_cDownUp_two_head_swap μ x a b (l₁ ++ l₂)
      (fun q hq => (List.mem_append.mp hq).elim (h1 q) (h2 q))]

/-- **Tasaki eq. (11.3.47) in canonical-Slater coefficients**: a flat-band ground state is an
explicit finite combination `Φ = Σ_s D(s)·generalFlatBandSlaterState μ (flatBandSpinConfigList σ_s)`
of the **canonical-list** Slater states, indexed by spin configurations `s : I → Fin 2`.  Unlike the
`flatBandSpinConfigState` coefficients (which differ from the canonical-Slater ones by the
existential `±1` sign of `flatBandSpinConfigState_eq_smul_canonical`), the `D(s)` are the genuine,
order-fixed coefficients of eqs. (11.3.47)–(11.3.49) — the canonical sorted order makes the sign
relation comparison clean. -/
theorem flatBand_groundState_eq_canonicalSlaterSum
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    ∃ D : (I → Fin 2) → ℂ,
      Φ = ∑ s, D s • generalFlatBandSlaterState μ
        (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0)) := by
  classical
  set ext : (I → Fin 2) → (Fin (M + 1) → Fin 2) :=
    fun s z => if h : z ∈ I then s ⟨z, h⟩ else 0 with hext_def
  -- Φ lies in the span of the `flatBandSpinConfigState` family (PR13's construction)
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
  -- the canonical-Slater family spans at least as much (they differ by a nonzero ±1 sign)
  have hle : Submodule.span ℂ
        (Set.range (fun s : I → Fin 2 => flatBandSpinConfigState I idx eμ (ext s)))
      ≤ Submodule.span ℂ
        (Set.range (fun s : I → Fin 2 =>
          generalFlatBandSlaterState μ (flatBandSpinConfigList I (ext s)))) := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    obtain ⟨z, _, hz⟩ := flatBandSpinConfigState_eq_smul_canonical hbasis hidx (ext s)
    simp only [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self s))
  obtain ⟨D, hD⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hle hmem)
  exact ⟨D, hD.symm⟩

end LatticeSystem.Fermion

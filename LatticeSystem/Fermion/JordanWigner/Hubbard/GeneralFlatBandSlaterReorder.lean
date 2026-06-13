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

/-- **The occupied-set of a one-erased nodup list** is the original set with the erased element
removed: for a nodup list `l` and `i < l.length`, `(l.eraseIdx i).toFinset = l.toFinset.erase l[i]`.
(Generic list fact; the engine behind tracking which mode a double-peel `eraseIdx` removes.) -/
theorem List.toFinset_eraseIdx_of_nodup {α : Type*} [DecidableEq α] {l : List α} (h : l.Nodup)
    {i : ℕ} (hi : i < l.length) :
    (l.eraseIdx i).toFinset = l.toFinset.erase l[i] := by
  ext q
  simp only [List.mem_toFinset, List.mem_eraseIdx_iff_getElem, Finset.mem_erase]
  constructor
  · rintro ⟨k, hk, hkne, rfl⟩
    exact ⟨fun hc => hkne ((List.Nodup.getElem_inj_iff h).mp hc), List.getElem_mem hk⟩
  · rintro ⟨hne, hmem⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨k, hk, fun hc => hne ((List.Nodup.getElem_inj_iff h).mpr hc), rfl⟩

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

/-- **The site double-annihilation of the canonical-list Slater state, as an explicit double peel**:
`ĉ_{x,↓}ĉ_{x,↑}` on `Slater(flatBandSpinConfigList σ)` expands (via the proved engine
`generalFlatBand_double_siteAnnihilation_peel`) into the position double-sum over the
orbital-ordered
canonical list — the explicit form whose terms are collected by removed index pair in the eq.
(11.3.48) reindexing step. -/
theorem cDownUp_canonical_eq_doublePeel (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2) (x : Fin (M + 1)) :
    (generalCDownUp M x).mulVec (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ))
      = ∑ i : Fin (flatBandSpinConfigList I σ).length,
          ((-1 : ℂ) ^ (i : ℕ)) •
            ((if ((flatBandSpinConfigList I σ).get i).2 = 0 then
                μ ((flatBandSpinConfigList I σ).get i).1 x else 0) •
              ∑ j : Fin ((flatBandSpinConfigList I σ).eraseIdx i).length,
                generalFlatBandPeelTerm μ x 1 ((flatBandSpinConfigList I σ).eraseIdx i) j) := by
  rw [generalCDownUp, ← Matrix.mulVec_mulVec,
    generalFlatBand_double_siteAnnihilation_peel μ x 0 1 (flatBandSpinConfigList I σ)]

/-- The canonical list has length `|I|` (one mode per index). -/
theorem flatBandSpinConfigList_length (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2) :
    (flatBandSpinConfigList I σ).length = I.card := by
  rw [flatBandSpinConfigList, List.length_map, Finset.length_sort]

/-- **Each canonical-list mode is `(z, σ z)`**: any element `q` of the canonical list satisfies
`q.2 = σ q.1`.  Lets the double-peel spin guard `[q].2 = ↑` be read as a condition on `σ` of the
index, in the eq. (11.3.48) reindexing. -/
theorem flatBandSpinConfigList_mem_snd_eq (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2)
    {q : Fin (M + 1) × Fin 2} (hq : q ∈ flatBandSpinConfigList I σ) : q.2 = σ q.1 := by
  rw [flatBandSpinConfigList, List.mem_map] at hq
  obtain ⟨z, _, hzq⟩ := hq
  rw [← hzq]

/-- The spin at position `i` of the canonical list equals `σ` of the index at position `i`. -/
theorem flatBandSpinConfigList_get_snd_eq (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2)
    (i : Fin (flatBandSpinConfigList I σ).length) :
    ((flatBandSpinConfigList I σ).get i).2 = σ ((flatBandSpinConfigList I σ).get i).1 :=
  flatBandSpinConfigList_mem_snd_eq I σ (List.get_mem _ i)

/-- **The occupation-basis coordinate of an occupation monomial is a Kronecker delta**:
`(generalOccBasis eμ).repr (occMon_eμ h) g = [h = g]`.  Since `occMon_eμ h` is the basis vector
`generalOccBasis eμ h`, its representation is `Finsupp.single h 1`.  This is the coordinate
functional that projects the eq. (11.3.48) double peel onto a fixed `(D₀−2)`-config in the
collection step. -/
theorem generalOccMonomial_repr (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (h g : Fin (M + 1) × Fin 2 → Fin 2) :
    (generalOccBasis eμ).repr (generalOccMonomial eμ h) g = if h = g then 1 else 0 := by
  have hb : generalOccMonomial eμ h = (generalOccBasis eμ) h :=
    (congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) h).symm
  rw [hb, Module.Basis.repr_self, Finsupp.single_apply]

/-- **Each mode of a one-erased canonical list is still `(z, σ z)`**: removing a position keeps the
remaining modes of the form `(z, σ z)`.  Lets the `(D₀−1)`/`(D₀−2)`-electron states produced by the
double peel be treated by the same spin-config machinery (they are spin-config lists over a smaller
index set). -/
theorem flatBandSpinConfigList_eraseIdx_mem_snd_eq (I : Finset (Fin (M + 1)))
    (σ : Fin (M + 1) → Fin 2) (i : ℕ) {q : Fin (M + 1) × Fin 2}
    (hq : q ∈ (flatBandSpinConfigList I σ).eraseIdx i) : q.2 = σ q.1 :=
  flatBandSpinConfigList_mem_snd_eq I σ (List.mem_of_mem_eraseIdx hq)

/-- A one-erased canonical list is still nodup. -/
theorem flatBandSpinConfigList_eraseIdx_nodup (I : Finset (Fin (M + 1)))
    (σ : Fin (M + 1) → Fin 2) (i : ℕ) :
    ((flatBandSpinConfigList I σ).eraseIdx i).Nodup :=
  (flatBandSpinConfigList_nodup I σ).eraseIdx i

/-- **Position ↔ index correspondence of the canonical list**: the mode at position `i` is
`(z_i, σ z_i)` where `z_i` is the `i`-th smallest index of `I`.  Pins each canonical-list position
to its index, the bookkeeping for collecting the double peel by removed index pair. -/
theorem flatBandSpinConfigList_getElem (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2)
    (i : ℕ) (hi : i < (I.sort (· ≤ ·)).length) :
    (flatBandSpinConfigList I σ)[i]'(by
        rwa [flatBandSpinConfigList_length, ← Finset.length_sort (· ≤ ·)])
      = ((I.sort (· ≤ ·))[i], σ ((I.sort (· ≤ ·))[i])) := by
  simp only [flatBandSpinConfigList, List.getElem_map]

/-- **The `(D₀−2)`-config coordinate of the canonical double peel**: applying the occupation-basis
coordinate functional `(generalOccBasis eμ).repr · g` to `ĉ_{x,↓}ĉ_{x,↑}Slater(canonical σ)`
distributes (by linearity) over the position double-sum, leaving the coordinates of the
doubly-erased
`(D₀−2)`-Slater states weighted by the peel amplitudes and Koszul signs.  This is the form on which
the removed-pair identification picks out, for a fixed `(D₀−2)`-target `g`, the unique contributing
`(i,j)`. -/
theorem cDownUp_canonical_repr_eq_sum (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2) (x : Fin (M + 1))
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (g : Fin (M + 1) × Fin 2 → Fin 2) :
    (generalOccBasis eμ).repr
        ((generalCDownUp M x).mulVec
          (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ))) g
      = ∑ i : Fin (flatBandSpinConfigList I σ).length,
          ((-1 : ℂ) ^ (i : ℕ)) *
            ((if ((flatBandSpinConfigList I σ).get i).2 = 0 then
                μ ((flatBandSpinConfigList I σ).get i).1 x else 0) *
              ∑ j : Fin ((flatBandSpinConfigList I σ).eraseIdx i).length,
                ((-1 : ℂ) ^ (j : ℕ)) *
                  ((if (((flatBandSpinConfigList I σ).eraseIdx i).get j).2 = 1 then
                      μ (((flatBandSpinConfigList I σ).eraseIdx i).get j).1 x else 0) *
                    (generalOccBasis eμ).repr (generalFlatBandSlaterState μ
                      (((flatBandSpinConfigList I σ).eraseIdx i).eraseIdx j)) g)) := by
  rw [cDownUp_canonical_eq_doublePeel]
  simp only [map_sum, map_smul, generalFlatBandPeelTerm, Finsupp.coe_finset_sum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **The occupation-basis coordinate of a `μ`-Slater state over `I`**: for a nodup list `qs` of
index modes (`q.1 ∈ I`), `(generalOccBasis eμ).repr (Slater μ qs) g` is a nonzero sign times the
Kronecker delta `[config(qs) = g]`, where `config(qs)` is the occupation indicator of the
`idx`-image
modes `{(idx z, σ) : (z,σ) ∈ qs}`.  This computes the coordinate of every `(D₀−2)`-Slater state
produced by the double peel (those `eraseIdx` lists are nodup over `I`).  Via the `μ`-Slater↔mode
monomial bridge (PR9), permutation scaling, and the occupation-monomial coordinate (PR25). -/
theorem generalFlatBandSlaterState_over_I_repr
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    (qs : List (Fin (M + 1) × Fin 2)) (hqs_nd : qs.Nodup) (hqs_I : ∀ q ∈ qs, q.1 ∈ I)
    (g : Fin (M + 1) × Fin 2 → Fin 2) :
    ∃ z : ℂ, z ≠ 0 ∧ (generalOccBasis eμ).repr (generalFlatBandSlaterState μ qs) g
      = z * (if (fun q => if q ∈ (qs.map (fun p => (idx p.1, p.2))).toFinset then (1 : Fin 2)
                else 0) = g then 1 else 0) := by
  classical
  set l : List (Fin (M + 1) × Fin 2) := qs.map (fun p => (idx p.1, p.2)) with hl
  have hl_nd : l.Nodup := by
    rw [hl]
    refine hqs_nd.map_on fun a ha b hb hab => ?_
    exact Prod.ext (flatBandSpecial_idx_injOn hbasis hidx (hqs_I a ha) (hqs_I b hb)
      (Prod.ext_iff.mp hab).1) (Prod.ext_iff.mp hab).2
  rw [generalFlatBandSlaterState_eq_generalModeMonomial eμ idx hidx qs hqs_I]
  set f : Fin (M + 1) × Fin 2 → Fin 2 := fun q => if q ∈ l.toFinset then 1 else 0 with hf
  have hocc : generalOccFinset f = l.toFinset := by
    ext q
    simp only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and, hf]
    by_cases h : q ∈ l.toFinset <;> simp [h]
  have hperm : l.Perm (generalOccFinset f).toList := by
    rw [hocc]; exact (List.toFinset_toList hl_nd).symm
  obtain ⟨z, hz0, hz⟩ := generalModeMonomial_perm eμ hperm
  refine ⟨z, hz0, ?_⟩
  rw [hz,
    show generalModeMonomial eμ (generalOccFinset f).toList = generalOccMonomial eμ f from rfl,
    map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, generalOccMonomial_repr]

/-- **The `idx`-image occupation config of a mode list**: the occupation indicator of the modes
`{(idx z, σ) : (z, σ) ∈ qs}`.  This is the `generalOccBasis eμ`-config that
`generalFlatBandSlaterState_over_I_repr` reads off; tracking it through `eraseIdx` identifies which
mode the double peel removes. -/
def idxConfigOf (idx : Fin (M + 1) → Fin (M + 1)) (qs : List (Fin (M + 1) × Fin 2)) :
    Fin (M + 1) × Fin 2 → Fin 2 :=
  fun q => if q ∈ (qs.map (fun p => (idx p.1, p.2))).toFinset then 1 else 0

/-- **One-erase of the `idx`-config**: removing position `i` from the list zeroes the config at the
removed mode `(idx qs[i].1, qs[i].2)` (requires the `idx`-image list nodup). -/
theorem idxConfigOf_eraseIdx
    (idx : Fin (M + 1) → Fin (M + 1)) (qs : List (Fin (M + 1) × Fin 2))
    (hnd : (qs.map (fun p => (idx p.1, p.2))).Nodup) (i : ℕ) (hi : i < qs.length) :
    idxConfigOf idx (qs.eraseIdx i)
      = Function.update (idxConfigOf idx qs) (idx (qs[i]'hi).1, (qs[i]'hi).2) 0 := by
  funext q
  have hi' : i < (qs.map (fun p => (idx p.1, p.2))).length := by rwa [List.length_map]
  simp only [idxConfigOf]
  rw [← List.eraseIdx_map, List.toFinset_eraseIdx_of_nodup hnd hi', List.getElem_map]
  simp only [Finset.mem_erase, Function.update_apply]
  by_cases hq : q = (idx (qs[i]'hi).1, (qs[i]'hi).2) <;> simp [hq, idxConfigOf]

/-- **Double-erase of the `idx`-config**: erasing positions `i` then `j` zeroes the config at the
two
removed modes `(idx qs[i].1, qs[i].2)` and `(idx (qs.eraseIdx i)[j].1, (qs.eraseIdx i)[j].2)`.  The
config of every `(D₀−2)`-Slater state produced by the double peel, in terms of the two removed
modes. -/
theorem idxConfigOf_eraseIdx_eraseIdx
    (idx : Fin (M + 1) → Fin (M + 1)) (qs : List (Fin (M + 1) × Fin 2))
    (hnd : (qs.map (fun p => (idx p.1, p.2))).Nodup) (i : ℕ) (hi : i < qs.length)
    (j : ℕ) (hj : j < (qs.eraseIdx i).length) :
    idxConfigOf idx ((qs.eraseIdx i).eraseIdx j)
      = Function.update
          (Function.update (idxConfigOf idx qs) (idx (qs[i]'hi).1, (qs[i]'hi).2) 0)
          (idx ((qs.eraseIdx i)[j]'hj).1, ((qs.eraseIdx i)[j]'hj).2) 0 := by
  have hnd' : ((qs.eraseIdx i).map (fun p => (idx p.1, p.2))).Nodup := by
    rw [← List.eraseIdx_map]; exact hnd.eraseIdx i
  rw [idxConfigOf_eraseIdx idx (qs.eraseIdx i) hnd' j hj,
    idxConfigOf_eraseIdx idx qs hnd i hi]

end LatticeSystem.Fermion

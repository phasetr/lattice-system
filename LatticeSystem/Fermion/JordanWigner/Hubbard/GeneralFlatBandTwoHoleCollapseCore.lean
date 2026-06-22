import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandCanonicalCoord

/-!
# Two-hole Slater coordinate collapse (eq. (11.3.49)): foundation

Foundational layer extracted from `GeneralFlatBandTwoHoleCollapse.lean` for build speed
(Tasaki §11.3.4, eq. (11.3.49)).  This file develops the canonical-position / sorted-finset
bookkeeping, the inner-sum collapse lemmas, the single-term two-hole coordinate
`cDownUp_canonical_repr_twoHole`, its sign flip under the `a ↔ b` spin swap
`cDownUp_canonical_repr_twoHole_swap_eq_neg` (the eq. (11.3.49) heart), and the
permutation-from-equal-weight helper.

The off-target vanishing `cDownUp_canonical_repr_eq_zero_of_ne` and the two-term sum
collapse `cDownUp_canonicalSum_eq_two_terms` are kept in the capstone module
`GeneralFlatBandTwoHoleCollapse.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §11.3.4 Theorem 11.17, eq. (11.3.49).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators ComplexOrder

variable {M : ℕ}


/-- **Two `Fin 2`-configs of equal weight differ by a permutation**: if `s, s' : I → Fin 2` have the
same number of `0`s, there is a permutation `π : Equiv.Perm I` with `s' ∘ π = s`.  Glue the
`Fintype.equivOfCardEq` bijections of the `0`-fibers and their complements through
`Equiv.sumCompl`.  (Generic fact; the engine behind "the ground-state coefficient depends only on
the up-count" in the eq. (11.3.49) connectivity induction.) -/
theorem exists_perm_comp_of_card_eq {I : Type*} [Fintype I] (s s' : I → Fin 2)
    (h : Fintype.card {z // s z = 0} = Fintype.card {z // s' z = 0}) :
    ∃ π : Equiv.Perm I, s' ∘ π = s := by
  classical
  have h1 : Fintype.card {z // ¬ s z = 0} = Fintype.card {z // ¬ s' z = 0} := by
    rw [Fintype.card_subtype_compl (fun z => s z = 0),
      Fintype.card_subtype_compl (fun z => s' z = 0), h]
  let e0 : {z // s z = 0} ≃ {z // s' z = 0} := Fintype.equivOfCardEq h
  let e1 : {z // ¬ s z = 0} ≃ {z // ¬ s' z = 0} := Fintype.equivOfCardEq h1
  refine ⟨(Equiv.sumCompl (fun z => s z = 0)).symm.trans
    ((e0.sumCongr e1).trans (Equiv.sumCompl (fun z => s' z = 0))), ?_⟩
  funext z
  rw [Function.comp_apply]
  by_cases hz : s z = 0
  · have hpi : ((Equiv.sumCompl (fun z => s z = 0)).symm.trans
        ((e0.sumCongr e1).trans (Equiv.sumCompl (fun z => s' z = 0)))) z = (e0 ⟨z, hz⟩).1 := by
      rw [Equiv.trans_apply, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_pos (p := fun w => s w = 0) hz,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    rw [hpi, (e0 ⟨z, hz⟩).2, hz]
  · have hpi : ((Equiv.sumCompl (fun z => s z = 0)).symm.trans
        ((e0.sumCongr e1).trans (Equiv.sumCompl (fun z => s' z = 0)))) z = (e1 ⟨z, hz⟩).1 := by
      rw [Equiv.trans_apply, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_neg (p := fun w => s w = 0) hz,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    rw [hpi]
    have he := (e1 ⟨z, hz⟩).2
    rcases fin2_eq_zero_or_one (s z) with h0 | h1x
    · exact absurd h0 hz
    · rcases fin2_eq_zero_or_one (s' (e1 ⟨z, hz⟩).1) with hh | hh
      · exact absurd hh he
      · rw [hh, h1x]

/-- **Inner-sum collapse (single peel)**: the inner `j`-sum of the canonical double peel, evaluated
at the `b`-emptied target config `idxConfigOf idx (canonical (S.erase b) σ)` (with `b ∈ S`,
`σ b = 1`) collapses to its single surviving term at the position of `b`.  Every off-position `j`
contributes
zero: by `flatBandSpinConfig_singlePeel_index_eq` the only `j` whose erased rest config hits the
target is the position of `b`, so all other `repr` coordinates vanish; at the position of `b` the
down-guard holds and the rest list is `canonical (S.erase b) σ`.  The surviving Koszul sign is
`(-1)` to the power of that position. -/
theorem flatBandSpinConfig_inner_sum_collapse {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) {S : Finset (Fin (M + 1))} (hS : S ⊆ I) {b : Fin (M + 1)} (hb : b ∈ S)
    (hσb : σ b = 1) :
    ∑ j : Fin (flatBandSpinConfigList S σ).length,
        ((-1 : ℂ) ^ (j : ℕ)) *
          ((if ((flatBandSpinConfigList S σ).get j).2 = 1 then
              μ ((flatBandSpinConfigList S σ).get j).1 x else 0) *
            (generalOccBasis eμ).repr (generalFlatBandSlaterState μ
              ((flatBandSpinConfigList S σ).eraseIdx j))
              (idxConfigOf idx (flatBandSpinConfigList (S.erase b) σ)))
      = ((-1 : ℂ) ^ ((flatBandSpinConfigList_existsUnique_pos S σ hb).choose : ℕ)) *
          (μ b x * (generalOccBasis eμ).repr (generalFlatBandSlaterState μ
            (flatBandSpinConfigList (S.erase b) σ))
            (idxConfigOf idx (flatBandSpinConfigList (S.erase b) σ))) := by
  have helper : ∀ j : Fin (flatBandSpinConfigList S σ).length,
      ((flatBandSpinConfigList S σ).get j).1 ≠ b →
      (generalOccBasis eμ).repr (generalFlatBandSlaterState μ
        ((flatBandSpinConfigList S σ).eraseIdx (j : ℕ)))
        (idxConfigOf idx (flatBandSpinConfigList (S.erase b) σ)) = 0 := by
    intro j hjb
    have hnd : ((flatBandSpinConfigList S σ).eraseIdx (j : ℕ)).Nodup :=
      flatBandSpinConfigList_eraseIdx_nodup S σ j
    have hsub : ∀ q ∈ (flatBandSpinConfigList S σ).eraseIdx (j : ℕ), q.1 ∈ I := fun q hq =>
      hS (flatBandSpinConfigList_mem_fst_mem S σ (List.mem_of_mem_eraseIdx hq))
    obtain ⟨z, _, heq⟩ := generalFlatBandSlaterState_over_I_repr hbasis eμ idx hidx
      ((flatBandSpinConfigList S σ).eraseIdx (j : ℕ)) hnd hsub
      (idxConfigOf idx (flatBandSpinConfigList (S.erase b) σ))
    rw [heq]
    split_ifs with hcond
    · refine absurd ?_ hjb
      rw [List.get_eq_getElem]
      exact flatBandSpinConfig_singlePeel_index_eq hbasis hidx σ hS j.2 hcond
    · ring
  obtain ⟨pb, hpb, huniq⟩ := flatBandSpinConfigList_existsUnique_pos S σ hb
  have hchoose : (flatBandSpinConfigList_existsUnique_pos S σ hb).choose = pb :=
    huniq _ (flatBandSpinConfigList_existsUnique_pos S σ hb).choose_spec.1
  rw [hchoose]
  have hXb : ((flatBandSpinConfigList S σ)[(pb:ℕ)]'pb.2).1 = b := by
    rw [← List.get_eq_getElem]; exact hpb
  have hlist : (flatBandSpinConfigList S σ).eraseIdx (pb : ℕ)
      = flatBandSpinConfigList (S.erase b) σ := by
    rw [flatBandSpinConfigList_eraseIdx S σ pb.2]
    exact congrArg (fun s => flatBandSpinConfigList (S.erase s) σ) hXb
  rw [Finset.sum_eq_single pb]
  · have hguard : ((flatBandSpinConfigList S σ).get pb).2 = 1 := by
      rw [flatBandSpinConfigList_get_snd_eq, hpb, hσb]
    rw [if_pos hguard, hpb, hlist]
  · intro j _ hjne
    have : ((flatBandSpinConfigList S σ).get j).1 ≠ b := fun hc => hjne (huniq j hc)
    rw [helper j this, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ pb) h

/-- **Wrong-outer vanishing**: if the outer-peeled index `c` is neither `a` nor `b`, the inner
`j`-sum over `canonical (I.erase c) σ` evaluated at the `(a,b)`-emptied target config is identically
zero.  Every term vanishes: by config injectivity and `Finset.eq_or_eq_of_erase_erase_eq`, no
single peel of `canonical (I.erase c) σ` can hit the `(a,b)`-emptied config (that would force
`c ∈ {a,b}`), so every `repr` coordinate is zero.  This is the off-diagonal case of the outer
`Finset.sum_eq_single` collapse of `cDownUp_canonical_repr_eq_sum`. -/
theorem flatBandSpinConfig_inner_sum_other_outer_zero {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) {a b c : Fin (M + 1)} (hcI : c ∈ I) (hca : c ≠ a) (hcb : c ≠ b) :
    ∑ j : Fin (flatBandSpinConfigList (I.erase c) σ).length,
        ((-1 : ℂ) ^ (j : ℕ)) *
          ((if ((flatBandSpinConfigList (I.erase c) σ).get j).2 = 1 then
              μ ((flatBandSpinConfigList (I.erase c) σ).get j).1 x else 0) *
            (generalOccBasis eμ).repr (generalFlatBandSlaterState μ
              ((flatBandSpinConfigList (I.erase c) σ).eraseIdx j))
              (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ))) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hnd : ((flatBandSpinConfigList (I.erase c) σ).eraseIdx (j : ℕ)).Nodup :=
    flatBandSpinConfigList_eraseIdx_nodup (I.erase c) σ j
  have hsub : ∀ q ∈ (flatBandSpinConfigList (I.erase c) σ).eraseIdx (j : ℕ), q.1 ∈ I := fun q hq =>
    Finset.mem_of_mem_erase
      (flatBandSpinConfigList_mem_fst_mem (I.erase c) σ (List.mem_of_mem_eraseIdx hq))
  obtain ⟨z, _, heq⟩ := generalFlatBandSlaterState_over_I_repr hbasis eμ idx hidx
    ((flatBandSpinConfigList (I.erase c) σ).eraseIdx (j : ℕ)) hnd hsub
    (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ))
  have hne : idxConfigOf idx ((flatBandSpinConfigList (I.erase c) σ).eraseIdx (j : ℕ))
      ≠ idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ) := by
    intro hcond'
    rw [flatBandSpinConfigList_eraseIdx (I.erase c) σ j.2] at hcond'
    have hset := idxConfigOf_flatBandSpinConfigList_inj hbasis hidx σ
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hcond'
    rcases Finset.eq_or_eq_of_erase_erase_eq hcI hset with h | h
    · exact hca h
    · exact hcb h
  rw [heq]
  split_ifs with hg hc <;> first | exact absurd hc hne | ring

/-- **The canonical double-peel coordinate collapses to a single term** (the eq. (11.3.49) heart):
for `a, b ∈ I`, `a ≠ b`, `σ a = 0` (up), `σ b = 1` (down), the coordinate of
`ĉ_{x,↓}ĉ_{x,↑}Slater(canonical I σ)` at the `(a,b)`-emptied target config collapses to the single
`(pos a, pos b)` term.  The outer `Finset.sum_eq_single` keeps only the outer position of `a` (the
up-guard forces an up index, uniquely `a`; every other outer index gives a vanishing inner sum by
`flatBandSpinConfig_inner_sum_other_outer_zero`), and at that position the inner sum collapses by
`flatBandSpinConfig_inner_sum_collapse` to the position of `b` in `I.erase a`.  The result is the
product of the two Koszul signs, `μ_a(x)`, `μ_b(x)`, and the shared `(D₀-2)`-electron rest
coordinate. -/
theorem cDownUp_canonical_repr_twoHole {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) {a b : Fin (M + 1)} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b)
    (hσa : σ a = 0) (hσb : σ b = 1) :
    (generalOccBasis eμ).repr
        ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ)))
        (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ))
      = ((-1 : ℂ) ^ ((flatBandSpinConfigList_existsUnique_pos I σ ha).choose : ℕ)) *
          (μ a x *
            (((-1 : ℂ) ^ ((flatBandSpinConfigList_existsUnique_pos (I.erase a) σ
                (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)).choose : ℕ)) *
              (μ b x * (generalOccBasis eμ).repr (generalFlatBandSlaterState μ
                (flatBandSpinConfigList ((I.erase a).erase b) σ))
                (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ))))) := by
  have hbea : b ∈ I.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  rw [cDownUp_canonical_repr_eq_sum]
  obtain ⟨pa, hpa, huniqa⟩ := flatBandSpinConfigList_existsUnique_pos I σ ha
  have hcha : (flatBandSpinConfigList_existsUnique_pos I σ ha).choose = pa :=
    huniqa _ (flatBandSpinConfigList_existsUnique_pos I σ ha).choose_spec.1
  rw [hcha, Finset.sum_eq_single pa]
  · have hguard : ((flatBandSpinConfigList I σ).get pa).2 = 0 := by
      rw [flatBandSpinConfigList_get_snd_eq, hpa, hσa]
    rw [if_pos hguard, hpa]
    have hXa : ((flatBandSpinConfigList I σ)[(pa:ℕ)]'pa.2).1 = a := by
      rw [← List.get_eq_getElem]; exact hpa
    rw [flatBandSpinConfigList_eraseIdx I σ pa.2,
      show ((flatBandSpinConfigList I σ)[(pa:ℕ)]'pa.2).1 = a from hXa,
      flatBandSpinConfig_inner_sum_collapse hbasis hidx σ x (Finset.erase_subset _ _) hbea hσb]
  · intro i _ hine
    by_cases hg : ((flatBandSpinConfigList I σ).get i).2 = 0
    · rw [if_pos hg]
      have hc : ((flatBandSpinConfigList I σ).get i).1 ≠ a := fun hca => hine (huniqa i hca)
      have hcb : ((flatBandSpinConfigList I σ).get i).1 ≠ b := by
        intro hcb'
        rw [flatBandSpinConfigList_get_snd_eq, hcb', hσb] at hg; exact absurd hg (by decide)
      have hcI : ((flatBandSpinConfigList I σ).get i).1 ∈ I :=
        flatBandSpinConfigList_mem_fst_mem I σ (List.get_mem _ _)
      have hXi : ((flatBandSpinConfigList I σ)[(i:ℕ)]'i.2).1
          = ((flatBandSpinConfigList I σ).get i).1 := by rw [List.get_eq_getElem]
      rw [flatBandSpinConfigList_eraseIdx I σ i.2, hXi,
        flatBandSpinConfig_inner_sum_other_outer_zero hbasis hidx σ x hcI hc hcb,
        mul_zero, mul_zero]
    · rw [if_neg hg, zero_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ pa) h

/-- **The index at a canonical position is the sorted-finset element there**:
`(canonical I σ).get p` has first component `(I.sort)[p]`, independent of `σ`.  (Destructuring `p`
to a bare `ℕ` index lets `List.getElem_map` fire without the `Fin`-length dependency that breaks a
direct rewrite.) -/
theorem flatBandSpinConfigList_get_fst_eq_sort (I : Finset (Fin (M + 1)))
    (σ : Fin (M + 1) → Fin 2) (p : Fin (flatBandSpinConfigList I σ).length)
    (hb : (p : ℕ) < (I.sort (· ≤ ·)).length) :
    ((flatBandSpinConfigList I σ).get p).1 = (I.sort (· ≤ ·))[(p : ℕ)]'hb := by
  obtain ⟨n, hn⟩ := p
  rw [List.get_eq_getElem]
  simp only [flatBandSpinConfigList, List.getElem_map]

/-- **The canonical position of an index is `σ`-independent**: the unique position carrying `z ∈ I`
is the same in `canonical I σ` and `canonical I σ'`, since the index sequence of the canonical list
is `I.sort` for every `σ`.  This lets the eq. (11.3.49) Koszul signs of `σ` and the spin-swapped
`σ_{a↔b}` be compared on the common `I.sort` positions. -/
theorem flatBandSpinConfigList_choose_eq (I : Finset (Fin (M + 1))) (σ σ' : Fin (M + 1) → Fin 2)
    {z : Fin (M + 1)} (hz : z ∈ I) :
    ((flatBandSpinConfigList_existsUnique_pos I σ hz).choose : ℕ)
      = ((flatBandSpinConfigList_existsUnique_pos I σ' hz).choose : ℕ) := by
  have hb1 : ((flatBandSpinConfigList_existsUnique_pos I σ hz).choose : ℕ)
      < (I.sort (· ≤ ·)).length := by
    rw [Finset.length_sort, ← flatBandSpinConfigList_length I σ]
    exact (flatBandSpinConfigList_existsUnique_pos I σ hz).choose.2
  have hb2 : ((flatBandSpinConfigList_existsUnique_pos I σ' hz).choose : ℕ)
      < (I.sort (· ≤ ·)).length := by
    rw [Finset.length_sort, ← flatBandSpinConfigList_length I σ']
    exact (flatBandSpinConfigList_existsUnique_pos I σ' hz).choose.2
  have h1 : (I.sort (· ≤ ·))[((flatBandSpinConfigList_existsUnique_pos I σ hz).choose : ℕ)]'hb1
      = z := by
    rw [← flatBandSpinConfigList_get_fst_eq_sort I σ _ hb1]
    exact (flatBandSpinConfigList_existsUnique_pos I σ hz).choose_spec.1
  have h2 : (I.sort (· ≤ ·))[((flatBandSpinConfigList_existsUnique_pos I σ' hz).choose : ℕ)]'hb2
      = z := by
    rw [← flatBandSpinConfigList_get_fst_eq_sort I σ' _ hb2]
    exact (flatBandSpinConfigList_existsUnique_pos I σ' hz).choose_spec.1
  exact (List.Nodup.getElem_inj_iff (I.sort_nodup _)).mp (h1.trans h2.symm)

/-- The canonical position of `z ∈ I` is a valid index into `I.sort`. -/
theorem flatBandSpinConfigList_choose_lt_sortLength (I : Finset (Fin (M + 1)))
    (σ : Fin (M + 1) → Fin 2) {z : Fin (M + 1)} (hz : z ∈ I) :
    ((flatBandSpinConfigList_existsUnique_pos I σ hz).choose : ℕ) < (I.sort (· ≤ ·)).length := by
  rw [Finset.length_sort, ← flatBandSpinConfigList_length I σ]
  exact (flatBandSpinConfigList_existsUnique_pos I σ hz).choose.2

/-- `I.sort` at the canonical position of `z ∈ I` is `z` itself. -/
theorem flatBandSpinConfigList_sort_getElem_choose (I : Finset (Fin (M + 1)))
    (σ : Fin (M + 1) → Fin 2) {z : Fin (M + 1)} (hz : z ∈ I) :
    (I.sort (· ≤ ·))[((flatBandSpinConfigList_existsUnique_pos I σ hz).choose : ℕ)]'
        (flatBandSpinConfigList_choose_lt_sortLength I σ hz) = z := by
  rw [← flatBandSpinConfigList_get_fst_eq_sort I σ _
    (flatBandSpinConfigList_choose_lt_sortLength I σ hz)]
  exact (flatBandSpinConfigList_existsUnique_pos I σ hz).choose_spec.1

/-- **eraseIdx position shift**: the canonical position of `b` in `I.erase a` equals its position in
`I` minus one when it sits to the right of `a`'s position: `pos_{I.erase a}(b) = pos_I(b) -
[pos_I(b) > pos_I(a)]`.  Identifying `(I.erase a).sort` with `(I.sort).eraseIdx pos_I(a)`
(`Finset.sort_eraseIdx_eq_sort_erase`), `List.getElem_eraseIdx` reads off the shifted index and
`I.sort` nodup inverts it.  This is the position arithmetic feeding `neg_one_pow_two_erase_shift`
for the eq. (11.3.49) sign comparison. -/
theorem flatBandSpinConfigList_choose_erase_shift (I : Finset (Fin (M + 1)))
    (σ : Fin (M + 1) → Fin 2) {a b : Fin (M + 1)} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    ((flatBandSpinConfigList_existsUnique_pos (I.erase a) σ
        (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)).choose : ℕ)
      = ((flatBandSpinConfigList_existsUnique_pos I σ hb).choose : ℕ)
        - (if ((flatBandSpinConfigList_existsUnique_pos I σ hb).choose : ℕ)
            > ((flatBandSpinConfigList_existsUnique_pos I σ ha).choose : ℕ) then 1 else 0) := by
  have hbea : b ∈ I.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hsa := flatBandSpinConfigList_sort_getElem_choose I σ ha
  have hsb := flatBandSpinConfigList_sort_getElem_choose I σ hb
  have hsQ := flatBandSpinConfigList_sort_getElem_choose (I.erase a) σ hbea
  have hnd : (I.sort (· ≤ ·)).Nodup := I.sort_nodup _
  have herase : (I.erase a).sort (· ≤ ·)
      = (I.sort (· ≤ ·)).eraseIdx
        ((flatBandSpinConfigList_existsUnique_pos I σ ha).choose : ℕ) := by
    rw [Finset.sort_eraseIdx_eq_sort_erase (· ≤ ·) I
      (flatBandSpinConfigList_choose_lt_sortLength I σ ha), hsa]
  have hsQ2 := (List.getElem_of_eq herase
    (flatBandSpinConfigList_choose_lt_sortLength (I.erase a) σ hbea)).symm.trans hsQ
  rw [List.getElem_eraseIdx] at hsQ2
  split_ifs at hsQ2 with hlt
  · have heq : ((flatBandSpinConfigList_existsUnique_pos (I.erase a) σ hbea).choose : ℕ)
        = ((flatBandSpinConfigList_existsUnique_pos I σ hb).choose : ℕ) :=
      (List.Nodup.getElem_inj_iff hnd).mp (hsQ2.trans hsb.symm)
    rw [heq, if_neg (by omega), Nat.sub_zero]
  · have hQ1 : ((flatBandSpinConfigList_existsUnique_pos (I.erase a) σ hbea).choose : ℕ) + 1
        = ((flatBandSpinConfigList_existsUnique_pos I σ hb).choose : ℕ) :=
      (List.Nodup.getElem_inj_iff hnd).mp (hsQ2.trans hsb.symm)
    rw [if_pos (by omega)]; omega

/-- **The two-hole coordinate flips sign under the `a↔b` spin swap** (eq. (11.3.49)): the coordinate
of `ĉ_{x,↓}ĉ_{x,↑}Slater(canonical I σ)` at the `(a,b)`-emptied config is the negative of the
coordinate for the spin-swapped `σ' = σ ∘ swap a b`.  Both collapse to a single term by
`cDownUp_canonical_repr_twoHole` (the swapped side with up/down roles exchanged, since `σ' a = 1`,
`σ' b = 0`); the rest Slater states coincide (`flatBandSpinConfigList_congr`, the rest set has no
`a, b`), the positions agree on `I.sort` (`flatBandSpinConfigList_choose_eq`) and shift by
`flatBandSpinConfigList_choose_erase_shift`, and the two Koszul signs are negatives by
`neg_one_pow_two_erase_shift`. -/
theorem cDownUp_canonical_repr_twoHole_swap_eq_neg {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) {a b : Fin (M + 1)} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b)
    (hσa : σ a = 0) (hσb : σ b = 1) :
    (generalOccBasis eμ).repr
        ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ (flatBandSpinConfigList I σ)))
        (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ))
      = - (generalOccBasis eμ).repr
          ((generalCDownUp M x).mulVec
            (generalFlatBandSlaterState μ (flatBandSpinConfigList I (σ ∘ ⇑(Equiv.swap a b)))))
          (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) := by
  set σ' := σ ∘ ⇑(Equiv.swap a b) with hσ'def
  have hba : b ≠ a := Ne.symm hab
  have hσ'a : σ' a = 1 := by simp only [hσ'def, Function.comp, Equiv.swap_apply_left]; exact hσb
  have hσ'b : σ' b = 0 := by simp only [hσ'def, Function.comp, Equiv.swap_apply_right]; exact hσa
  have hbeb : a ∈ I.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
  have hrest : flatBandSpinConfigList ((I.erase b).erase a) σ'
      = flatBandSpinConfigList ((I.erase a).erase b) σ := by
    rw [Finset.erase_right_comm]
    apply flatBandSpinConfigList_congr
    intro z hz
    have hzb : z ≠ b := fun h => (Finset.mem_erase.mp hz).1 h
    have hza : z ≠ a := fun h => (Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)).1 h
    simp only [hσ'def, Function.comp, Equiv.swap_apply_of_ne_of_ne hza hzb]
  rw [cDownUp_canonical_repr_twoHole hbasis hidx σ x ha hb hab hσa hσb]
  rw [show idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)
      = idxConfigOf idx (flatBandSpinConfigList ((I.erase b).erase a) σ') from by rw [hrest]]
  rw [cDownUp_canonical_repr_twoHole hbasis hidx σ' x hb ha hba hσ'b hσ'a]
  rw [hrest]
  rw [flatBandSpinConfigList_choose_eq I σ' σ hb]
  rw [flatBandSpinConfigList_choose_eq (I.erase b) σ' σ hbeb]
  rw [flatBandSpinConfigList_choose_erase_shift I σ ha hb hab]
  rw [flatBandSpinConfigList_choose_erase_shift I σ hb ha hba]
  have hsortnd : (I.sort (· ≤ ·)).Nodup := I.sort_nodup _
  have hva := flatBandSpinConfigList_sort_getElem_choose I σ ha
  have hvb := flatBandSpinConfigList_sort_getElem_choose I σ hb
  have hPab : ((flatBandSpinConfigList_existsUnique_pos I σ ha).choose : ℕ)
      ≠ ((flatBandSpinConfigList_existsUnique_pos I σ hb).choose : ℕ) := fun h =>
    hab (hva.symm.trans (((List.Nodup.getElem_inj_iff hsortnd).mpr h).trans hvb))
  have hsign : (-1 : ℂ) ^ ((flatBandSpinConfigList_existsUnique_pos I σ ha).choose : ℕ)
        * (-1) ^ (((flatBandSpinConfigList_existsUnique_pos I σ hb).choose : ℕ)
          - (if ((flatBandSpinConfigList_existsUnique_pos I σ hb).choose : ℕ)
              > ((flatBandSpinConfigList_existsUnique_pos I σ ha).choose : ℕ) then 1 else 0))
      = -((-1 : ℂ) ^ ((flatBandSpinConfigList_existsUnique_pos I σ hb).choose : ℕ)
        * (-1) ^ (((flatBandSpinConfigList_existsUnique_pos I σ ha).choose : ℕ)
          - (if ((flatBandSpinConfigList_existsUnique_pos I σ ha).choose : ℕ)
              > ((flatBandSpinConfigList_existsUnique_pos I σ hb).choose : ℕ) then 1 else 0))) := by
    rw [← pow_add, ← pow_add]; exact neg_one_pow_two_erase_shift _ _ hPab
  linear_combination (μ a x * μ b x * (generalOccBasis eμ).repr
    (generalFlatBandSlaterState μ (flatBandSpinConfigList ((I.erase a).erase b) σ))
    (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ))) * hsign

/-- **A contributing double peel forces the Slater config to be `σ` or its `a↔b` swap** (the
`σ`-varying determination feeding the eq. (11.3.49) sum collapse): if the doubly-erased rest config
of `Slater(canonical I τ)` equals the `(a,b)`-emptied target `idxConfigOf idx (canonical
((I.erase a).erase b) σ)` (with `σ a = 0`, `σ b = 1`) and the peel guards hold (outer up, inner
down), then on `I` either `τ = σ` or `τ = σ ∘ swap a b`.  The `σ`-varying config injectivity
(`idxConfigOf_flatBandSpinConfigList_inj_gen`) forces the twice-erased set to match and `τ = σ` off
`{a,b}`; `Finset.eq_or_eq_of_erase_erase_eq` pins the removed pair to `{a,b}`, and the guards fix
the two spins of `τ` at `a, b` to `0, 1` in one of the two orders. -/
theorem flatBandSpinConfig_doublePeel_config_eq {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ τ : Fin (M + 1) → Fin 2)
    {a b : Fin (M + 1)} (hσa : σ a = 0) (hσb : σ b = 1)
    {i : ℕ} (hi : i < (flatBandSpinConfigList I τ).length)
    (hgi : ((flatBandSpinConfigList I τ)[i]).2 = 0) {j : ℕ}
    (hj : j < (flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I τ)[i]).1) τ).length)
    (hgj : ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I τ)[i]).1) τ)[j]).2 = 1)
    (hconfig : idxConfigOf idx (((flatBandSpinConfigList I τ).eraseIdx i).eraseIdx j)
      = idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) :
    (∀ z ∈ I, τ z = σ z) ∨ (∀ z ∈ I, τ z = (σ ∘ ⇑(Equiv.swap a b)) z) := by
  have hcI : ((flatBandSpinConfigList I τ)[i]).1 ∈ I :=
    flatBandSpinConfigList_mem_fst_mem I τ (List.getElem_mem _)
  have hdI : ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I τ)[i]).1) τ)[j]).1 ∈ I :=
    Finset.mem_of_mem_erase (flatBandSpinConfigList_mem_fst_mem _ τ (List.getElem_mem _))
  rw [flatBandSpinConfigList_eraseIdx_eraseIdx I τ hi hj] at hconfig
  obtain ⟨hset, hspin⟩ := idxConfigOf_flatBandSpinConfigList_inj_gen hbasis hidx τ σ
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hconfig
  have hτc : τ ((flatBandSpinConfigList I τ)[i]).1 = 0 := by
    rw [← flatBandSpinConfigList_mem_snd_eq I τ (List.getElem_mem hi)]; exact hgi
  have hτd :
      τ ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I τ)[i]).1) τ)[j]).1 = 1 := by
    rw [← flatBandSpinConfigList_mem_snd_eq _ τ (List.getElem_mem hj)]; exact hgj
  set c := ((flatBandSpinConfigList I τ)[i]).1 with hcdef
  set d := ((flatBandSpinConfigList (I.erase c) τ)[j]).1 with hddef
  have hcd : c ≠ d := fun h => by rw [h, hτd] at hτc; exact absurd hτc (by decide)
  have hc := Finset.eq_or_eq_of_erase_erase_eq hcI hset
  rw [Finset.erase_right_comm] at hset
  have hd := Finset.eq_or_eq_of_erase_erase_eq hdI hset
  rcases hc with hca | hcb
  · left
    have hdb : d = b := by
      rcases hd with h | h
      · exact absurd (hca.trans h.symm) hcd
      · exact h
    intro z hzI
    by_cases hza : z = a
    · rw [hza, hσa, ← hca]; exact hτc
    · by_cases hzb : z = b
      · rw [hzb, hσb, ← hdb]; exact hτd
      · exact hspin z (Finset.mem_erase.mpr ⟨(fun h => hzb (h.trans hdb)),
          Finset.mem_erase.mpr ⟨(fun h => hza (h.trans hca)), hzI⟩⟩)
  · right
    have hda : d = a := by
      rcases hd with h | h
      · exact h
      · exact absurd (hcb.trans h.symm) hcd
    intro z hzI
    by_cases hza : z = a
    · rw [hza, show (σ ∘ ⇑(Equiv.swap a b)) a = 1 from by
        simp only [Function.comp, Equiv.swap_apply_left]; exact hσb, ← hda]; exact hτd
    · by_cases hzb : z = b
      · rw [hzb, show (σ ∘ ⇑(Equiv.swap a b)) b = 0 from by
          simp only [Function.comp, Equiv.swap_apply_right]; exact hσa, ← hcb]; exact hτc
      · have hz := hspin z (Finset.mem_erase.mpr ⟨(fun h => hza (h.trans hda)),
          Finset.mem_erase.mpr ⟨(fun h => hzb (h.trans hcb)), hzI⟩⟩)
        rw [hz]; simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hza hzb]

end LatticeSystem.Fermion

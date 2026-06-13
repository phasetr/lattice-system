import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandCanonicalCoord

/-!
# Two-hole double-peel collapse and the eq. (11.3.49) sign flip (Tasaki §11.3.4)

The collapse of the canonical double peel `ĉ_{x,↓}ĉ_{x,↑}Slater(canonical I σ)` to a single term at
the `(a,b)`-emptied target config, and the resulting Koszul sign flip under the `a↔b` spin swap.
Built on the determination lemmas in `GeneralFlatBandCanonicalCoord.lean`: the inner-sum collapse
(`flatBandSpinConfig_inner_sum_collapse`) and its off-diagonal vanishing
(`flatBandSpinConfig_inner_sum_other_outer_zero`), the single-term coordinate
`cDownUp_canonical_repr_twoHole`, the `σ`-independence and eraseIdx position arithmetic of canonical
positions (`flatBandSpinConfigList_choose_eq`, `flatBandSpinConfigList_choose_erase_shift`), and the
sign flip `cDownUp_canonical_repr_twoHole_swap_eq_neg` (= `coord_σ = -coord_{σ∘swap}`).

Split from `GeneralFlatBandCanonicalCoord.lean` (the coordinate/config/determination machinery) for
build speed.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.49).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators ComplexOrder

variable {M : ℕ}

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

/-- **A flat-band Slater coordinate vanishes off the two relevant spin configs** (the eq. (11.3.49)
sum-collapse engine): if `τ` is neither `σ` nor `σ ∘ swap a b` on `I`, then the `(a,b)`-emptied
coordinate of `ĉ_{x,↓}ĉ_{x,↑}Slater(canonical I τ)` is zero.  Each double-peel term of
`cDownUp_canonical_repr_eq_sum` vanishes: a term with both guards (outer up, inner down) holding and
nonzero rest coordinate would force the config equality of
`flatBandSpinConfig_doublePeel_config_eq`, hence `τ = σ` or `τ = σ ∘ swap a b` on `I`, contradicting
the hypotheses; the other terms vanish by the failing guard. -/
theorem cDownUp_canonical_repr_eq_zero_of_ne {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ τ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) {a b : Fin (M + 1)} (hσa : σ a = 0) (hσb : σ b = 1)
    (hne1 : ¬ ∀ z ∈ I, τ z = σ z) (hne2 : ¬ ∀ z ∈ I, τ z = (σ ∘ ⇑(Equiv.swap a b)) z) :
    (generalOccBasis eμ).repr
        ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ (flatBandSpinConfigList I τ)))
        (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) = 0 := by
  -- per-(i,j) helper
  have hterm : ∀ (i : ℕ) (hi : i < (flatBandSpinConfigList I τ).length),
      ((flatBandSpinConfigList I τ)[i]).2 = 0 →
      ∀ (j : ℕ) (hj : j <
        (flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I τ)[i]).1) τ).length),
      ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I τ)[i]).1) τ)[j]).2 = 1 →
      (generalOccBasis eμ).repr (generalFlatBandSlaterState μ
        (((flatBandSpinConfigList I τ).eraseIdx i).eraseIdx j))
        (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) = 0 := by
    intro i hi hgi j hj hgj
    have hnd : (((flatBandSpinConfigList I τ).eraseIdx i).eraseIdx j).Nodup := by
      rw [flatBandSpinConfigList_eraseIdx_eraseIdx I τ hi hj]
      exact flatBandSpinConfigList_nodup _ _
    have hsub : ∀ q ∈ ((flatBandSpinConfigList I τ).eraseIdx i).eraseIdx j, q.1 ∈ I := by
      rw [flatBandSpinConfigList_eraseIdx_eraseIdx I τ hi hj]
      intro q hq
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
        (flatBandSpinConfigList_mem_fst_mem _ τ hq))
    obtain ⟨z, _, heq⟩ := generalFlatBandSlaterState_over_I_repr hbasis eμ idx hidx
      (((flatBandSpinConfigList I τ).eraseIdx i).eraseIdx j) hnd hsub _
    rw [heq]
    split_ifs with hcond
    · exfalso
      rcases flatBandSpinConfig_doublePeel_config_eq hbasis hidx σ τ hσa hσb hi hgi hj hgj hcond
        with h | h
      · exact hne1 h
      · exact hne2 h
    · ring
  -- main
  rw [cDownUp_canonical_repr_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hgi : ((flatBandSpinConfigList I τ).get i).2 = 0
  · rw [if_pos hgi]
    have hgi' : ((flatBandSpinConfigList I τ)[(i:ℕ)]'i.2).2 = 0 := by
      rw [← List.get_eq_getElem]; exact hgi
    have hpr38 := flatBandSpinConfigList_eraseIdx I τ i.2
    rw [Finset.sum_eq_zero, mul_zero, mul_zero]
    intro j _
    by_cases hgj : (((flatBandSpinConfigList I τ).eraseIdx (i:ℕ)).get j).2 = 1
    · have hjc : (j : ℕ) < (flatBandSpinConfigList
          (I.erase ((flatBandSpinConfigList I τ)[(i:ℕ)]'i.2).1) τ).length := by
        rw [← hpr38]; exact j.2
      have hgjc : ((flatBandSpinConfigList
          (I.erase ((flatBandSpinConfigList I τ)[(i:ℕ)]'i.2).1) τ)[(j:ℕ)]'hjc).2 = 1 := by
        rw [← List.getElem_of_eq hpr38 j.2, ← List.get_eq_getElem]; exact hgj
      rw [if_pos hgj, hterm (i:ℕ) i.2 hgi' (j:ℕ) hjc hgjc, mul_zero, mul_zero]
    · rw [if_neg hgj, zero_mul, mul_zero]
  · rw [if_neg hgi, zero_mul, mul_zero]

/-- **The ground-state coordinate sum collapses to two terms** (the eq. (11.3.49) sum collapse):
summing the `(a,b)`-emptied coordinate of `ĉ_{x,↓}ĉ_{x,↑}Slater` over all spin configs
`s : I → Fin 2` (weighted by `D s`) keeps only the two configs `σ|_I` and `(σ ∘ swap a b)|_I`, every
other config
contributing zero by `cDownUp_canonical_repr_eq_zero_of_ne`. -/
theorem cDownUp_canonicalSum_eq_two_terms {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) {a b : Fin (M + 1)} (ha : a ∈ I) (_hb : b ∈ I) (_hab : a ≠ b)
    (hσa : σ a = 0) (hσb : σ b = 1) (D : (I → Fin 2) → ℂ) :
    ∑ s : I → Fin 2, D s * (generalOccBasis eμ).repr
        ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ
          (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))))
        (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ))
      = D (fun z : I => σ z.1) * (generalOccBasis eμ).repr
          ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ
            (flatBandSpinConfigList I
              (fun z => if h : z ∈ I then (fun z : I => σ z.1) ⟨z, h⟩ else 0))))
          (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ))
        + D (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1) * (generalOccBasis eμ).repr
          ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ
            (flatBandSpinConfigList I (fun z => if h : z ∈ I then
              (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1) ⟨z, h⟩ else 0))))
          (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) := by
  have hne : (fun z : I => σ z.1) ≠ (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1) := by
    intro h
    have := congrFun h ⟨a, ha⟩
    simp only [Function.comp, Equiv.swap_apply_left, hσa, hσb] at this
    exact absurd this (by decide)
  rw [← Finset.sum_subset (Finset.subset_univ {(fun z : I => σ z.1),
      (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1)})]
  · rw [Finset.sum_pair hne]
  · intro s _ hs
    rw [Finset.mem_insert, Finset.mem_singleton] at hs
    push Not at hs
    have hvanish := cDownUp_canonical_repr_eq_zero_of_ne hbasis hidx σ
      (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0) x hσa hσb
      (by intro hh; apply hs.1; funext z; have := hh z.1 z.2; simpa [z.2] using this)
      (by intro hh; apply hs.2; funext z; have := hh z.1 z.2; simpa [z.2] using this)
    rw [hvanish, mul_zero]

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

end LatticeSystem.Fermion

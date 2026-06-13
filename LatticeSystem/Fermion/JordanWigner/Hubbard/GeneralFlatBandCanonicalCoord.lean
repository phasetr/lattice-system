import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandSlaterReorder

/-!
# Canonical creation-list coordinates and erased-index configs (Tasaki §11.3.4, eq. 11.3.48)

The coordinate/config bookkeeping for the eq. (11.3.48) double-annihilation sign relation: the
length and per-mode shape of the canonical (sorted) spin-config creation list, the occupation-basis
coordinate functional `generalOccMonomial_repr` and its distribution over the positional
double-peel sum `cDownUp_canonical_repr_eq_sum`, the index-configuration `idxConfigOf` of a Slater
state and how it tracks single/double `eraseIdx` removals, the position↔index correspondence
(`flatBandSpinConfigList_getElem`, `_get_fst_inj`, `_existsUnique_pos`), and the
erase-to-canonical bridge `flatBandSpinConfigList_eraseIdx` reducing the inner peel list to a
canonical creation list over a smaller index set.

Split from `GeneralFlatBandSlaterReorder.lean` (the reorder/extraction machinery) for build speed.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eqs. (11.3.48)–(11.3.49).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators ComplexOrder

variable {M : ℕ}

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

/-- **The `idx`-config of the canonical list is the spin-configuration occupation**:
`idxConfigOf idx (flatBandSpinConfigList I σ) = flatBandSpinConfigOcc I idx σ`.  Connects the
`eraseIdx`-tracking config to the established spin-config-occupation machinery (PR9–PR11), so the
`(D₀−2)`-target configs are expressed via `flatBandSpinConfigOcc`. -/
theorem idxConfigOf_flatBandSpinConfigList (I : Finset (Fin (M + 1)))
    (idx : Fin (M + 1) → Fin (M + 1)) (σ : Fin (M + 1) → Fin 2) :
    idxConfigOf idx (flatBandSpinConfigList I σ) = flatBandSpinConfigOcc I idx σ := by
  funext q
  simp only [idxConfigOf, flatBandSpinConfigList, List.map_map, List.mem_toFinset, List.mem_map,
    Finset.mem_sort, Function.comp_apply, flatBandSpinConfigOcc]
  by_cases h : ∃ z ∈ I, q = (idx z, σ z)
  · obtain ⟨z, hz, rfl⟩ := h
    rw [if_pos ⟨z, hz, rfl⟩, if_pos ⟨z, hz, rfl⟩]
  · rw [if_neg, if_neg h]
    rintro ⟨z, hz, hzq⟩
    exact h ⟨z, hz, hzq.symm⟩

/-- **Distinct canonical-list positions carry distinct indices**: the first-coordinate (index) at
position `i` determines `i`.  Since each mode is `(z, σ z)` and the list is nodup, equal indices
give
equal modes give equal positions.  The injectivity behind "exactly one `(i,j)` per removed pair". -/
theorem flatBandSpinConfigList_get_fst_inj (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2)
    {i i' : Fin (flatBandSpinConfigList I σ).length}
    (h : ((flatBandSpinConfigList I σ).get i).1 = ((flatBandSpinConfigList I σ).get i').1) :
    i = i' := by
  have he : (flatBandSpinConfigList I σ).get i = (flatBandSpinConfigList I σ).get i' :=
    Prod.ext h (by rw [flatBandSpinConfigList_get_snd_eq I σ i,
      flatBandSpinConfigList_get_snd_eq I σ i', h])
  exact (List.nodup_iff_injective_get.mp (flatBandSpinConfigList_nodup I σ)) he

/-- **Each index of `I` occurs in the canonical list**: `z ∈ I → (z, σ z) ∈ flatBandSpinConfigList
I σ`. -/
theorem flatBandSpinConfigList_mem (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2)
    {z : Fin (M + 1)} (hz : z ∈ I) : (z, σ z) ∈ flatBandSpinConfigList I σ :=
  List.mem_map.mpr ⟨z, Finset.mem_sort _ |>.mpr hz, rfl⟩

/-- **Existence of the canonical-list position of an index**: for `z ∈ I` there is a position whose
mode is `(z, σ z)`.  With `flatBandSpinConfigList_get_fst_inj` (uniqueness), this pins the unique
position carrying each index — the bookkeeping for "exactly one `(i,j)` per removed pair". -/
theorem flatBandSpinConfigList_exists_pos (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2)
    {z : Fin (M + 1)} (hz : z ∈ I) :
    ∃ i : Fin (flatBandSpinConfigList I σ).length, (flatBandSpinConfigList I σ).get i = (z, σ z) :=
  List.get_of_mem (flatBandSpinConfigList_mem I σ hz)

/-- **Each index of `I` sits at a unique canonical-list position**: for `z ∈ I` there is exactly one
position `i` with index `z` (existence `flatBandSpinConfigList_exists_pos` + uniqueness
`flatBandSpinConfigList_get_fst_inj`).  This is the position-of-index bookkeeping that makes the
double-peel `(i,j)` of a removed pair unique. -/
theorem flatBandSpinConfigList_existsUnique_pos (I : Finset (Fin (M + 1)))
    (σ : Fin (M + 1) → Fin 2) {z : Fin (M + 1)} (hz : z ∈ I) :
    ∃! i : Fin (flatBandSpinConfigList I σ).length, ((flatBandSpinConfigList I σ).get i).1 = z := by
  obtain ⟨i, hi⟩ := flatBandSpinConfigList_exists_pos I σ hz
  refine ⟨i, by simp only [hi], fun i' hi' => flatBandSpinConfigList_get_fst_inj I σ ?_⟩
  rw [hi', hi]

/-- **Erasing a canonical-list position gives the canonical list of the erased index set**:
`(flatBandSpinConfigList I σ).eraseIdx i = flatBandSpinConfigList (I.erase L[i].1) σ`.  Combining
`List.eraseIdx_map` with `Finset.sort_eraseIdx_eq_sort_erase`, the inner double-peel list over the
positions of the canonical creation list is itself a canonical creation list over `I.erase L[i].1`,
so the `(D₀-2)`-electron "rest" states reuse the canonical machinery (`existsUnique_pos`,
`idxConfigOf`, the bridge `repr`) over the smaller index set. -/
theorem flatBandSpinConfigList_eraseIdx (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2)
    {i : ℕ} (hi : i < (flatBandSpinConfigList I σ).length) :
    (flatBandSpinConfigList I σ).eraseIdx i
      = flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I σ)[i]).1) σ := by
  have hsort : i < (I.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; rw [flatBandSpinConfigList_length] at hi; exact hi
  rw [flatBandSpinConfigList_getElem]
  conv_lhs => rw [flatBandSpinConfigList, List.eraseIdx_map,
    Finset.sort_eraseIdx_eq_sort_erase (· ≤ ·) I hsort]
  rfl

/-- **Coordinate value of a single inner peel term**: the occupation-basis coordinate functional
distributes over `generalFlatBandPeelTerm` as `repr (peelTerm μ x s qs i) g`
`= (-1)^i · [qs[i].2 = s] · μ_{qs[i].1}(x) · repr (Slater (qs.eraseIdx i)) g`.
The inner `j`-sum of the canonical double peel (`cDownUp_canonical_repr_eq_sum`) is term-wise of
this form, so collecting it at a target config `g` reduces to the bridge coordinate
`generalFlatBandSlaterState_over_I_repr` of the double-erased "rest" Slater state. -/
theorem generalFlatBandPeelTerm_repr (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (x : Fin (M + 1))
    (s : Fin 2) (qs : List (Fin (M + 1) × Fin 2)) (i : Fin qs.length)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (g : Fin (M + 1) × Fin 2 → Fin 2) :
    (generalOccBasis eμ).repr (generalFlatBandPeelTerm μ x s qs i) g
      = (-1 : ℂ) ^ (i : ℕ) * (if (qs.get i).2 = s then μ (qs.get i).1 x else 0)
          * (generalOccBasis eμ).repr (generalFlatBandSlaterState μ (qs.eraseIdx i)) g := by
  simp only [generalFlatBandPeelTerm, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Erasing two canonical-list positions gives the canonical list of the twice-erased index set**:
applying `flatBandSpinConfigList_eraseIdx` twice, the double-peel "rest" list
`((flatBandSpinConfigList I σ).eraseIdx i).eraseIdx j` is the canonical creation list over
`(I.erase a).erase b` with `a = L[i].1` and `b` the index at position `j` of the once-erased
canonical list.  This identifies the `(D₀-2)`-electron rest Slater state, so its coordinate is read
off by `generalFlatBandSlaterState_over_I_repr` over the smaller index set. -/
theorem flatBandSpinConfigList_eraseIdx_eraseIdx (I : Finset (Fin (M + 1)))
    (σ : Fin (M + 1) → Fin 2) {i : ℕ} (hi : i < (flatBandSpinConfigList I σ).length) {j : ℕ}
    (hj : j < (flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I σ)[i]).1) σ).length) :
    ((flatBandSpinConfigList I σ).eraseIdx i).eraseIdx j
      = flatBandSpinConfigList ((I.erase ((flatBandSpinConfigList I σ)[i]).1).erase
          ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I σ)[i]).1) σ)[j]).1) σ := by
  rw [flatBandSpinConfigList_eraseIdx I σ hi, flatBandSpinConfigList_eraseIdx _ σ hj]

/-- **The canonical list depends on `σ` only through its values on the index set**: if `σ` and `σ'`
agree on every `z ∈ S` then `flatBandSpinConfigList S σ = flatBandSpinConfigList S σ'`.  Applied to
the twice-erased set `(I.erase a).erase b` (containing neither `a` nor `b`), the `(D₀-2)`-electron
rest list is the *same* for `σ` and the spin-swapped `σ_{a↔b}` (they agree off `{a,b}`), so the
shared rest Slater state's nonzero bridge coefficient cancels in the eq. (11.3.49) comparison
`D(σ) = D(σ_{a↔b})` instead of requiring an existential sign comparison. -/
theorem flatBandSpinConfigList_congr (S : Finset (Fin (M + 1))) (σ σ' : Fin (M + 1) → Fin 2)
    (h : ∀ z ∈ S, σ z = σ' z) : flatBandSpinConfigList S σ = flatBandSpinConfigList S σ' := by
  unfold flatBandSpinConfigList
  apply List.map_congr_left
  intro z hz
  rw [h z ((Finset.mem_sort (· ≤ ·)).mp hz)]

end LatticeSystem.Fermion

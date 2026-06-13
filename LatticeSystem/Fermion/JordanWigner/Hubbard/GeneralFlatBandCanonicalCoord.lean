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

/-- **An element erased on the left lies in the pair erased on the right**: if `c ∈ I` and
`(I.erase c).erase d = (I.erase a).erase b` then `c = a ∨ c = b`.  (Generic finset fact; the engine
disambiguating which removed index pair a double-peel "rest" set came from in the eq. (11.3.49)
collapse — applied to both removed indices it pins the unordered pair to `{a,b}`.) -/
theorem Finset.eq_or_eq_of_erase_erase_eq {α : Type*} [DecidableEq α] {I : Finset α} {a b c d : α}
    (hc : c ∈ I) (h : (I.erase c).erase d = (I.erase a).erase b) : c = a ∨ c = b := by
  have hcL : c ∉ (I.erase c).erase d := by simp [Finset.mem_erase]
  rw [h] at hcL
  simp only [Finset.mem_erase] at hcL
  push Not at hcL
  by_contra hcon
  push Not at hcon
  exact (hcL hcon.2 hcon.1) hc

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

/-- **Every canonical-list mode is indexed in `I`**: any element `q` of `flatBandSpinConfigList I σ`
has `q.1 ∈ I`.  Supplies the `∀ q ∈ qs, q.1 ∈ I` hypothesis of
`generalFlatBandSlaterState_over_I_repr` for canonical lists and the `(D₀-2)`-electron rest lists
derived from them by `eraseIdx`. -/
theorem flatBandSpinConfigList_mem_fst_mem (I : Finset (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2)
    {q : Fin (M + 1) × Fin 2} (hq : q ∈ flatBandSpinConfigList I σ) : q.1 ∈ I := by
  simp only [flatBandSpinConfigList, List.mem_map, Finset.mem_sort] at hq
  obtain ⟨z, hz, rfl⟩ := hq
  exact hz

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

/-- **A `μ`-Slater state over `I` has nonzero coordinate at its own index config**: evaluating the
bridge coordinate `generalFlatBandSlaterState_over_I_repr` at `g = idxConfigOf idx qs` (its own
occupied config) forces the indicator to `1`, leaving the nonzero scalar `z`.  This is the `R ≠ 0`
fact cancelled in the eq. (11.3.49) relation `D(σ) = D(σ_{a↔b})`: the shared `(D₀-2)`-electron rest
Slater state has nonzero coordinate at the rest config, so it can be divided out. -/
theorem generalFlatBandSlaterState_repr_self_ne_zero
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z)
    (qs : List (Fin (M + 1) × Fin 2)) (hqs_nd : qs.Nodup) (hqs_I : ∀ q ∈ qs, q.1 ∈ I) :
    (generalOccBasis eμ).repr (generalFlatBandSlaterState μ qs) (idxConfigOf idx qs) ≠ 0 := by
  obtain ⟨z, hz, heq⟩ :=
    generalFlatBandSlaterState_over_I_repr hbasis eμ idx hidx qs hqs_nd hqs_I (idxConfigOf idx qs)
  rw [heq]
  have hc : (fun q => if q ∈ (qs.map (fun p => (idx p.1, p.2))).toFinset then (1 : Fin 2) else 0)
      = idxConfigOf idx qs := rfl
  rw [hc, if_pos rfl, mul_one]
  exact hz

/-- **The index config of a canonical creation list determines its index set**: for `S, S' ⊆ I`
(with `idx` injective on `I`), if `idxConfigOf idx (canonical S σ)` equals
`idxConfigOf idx (canonical S' σ)` then `S = S'`.  Evaluating the config at the mode `(idx w, σ w)`
reads off `w ∈ S` (the indicator
is `1` exactly there), so equal configs force equal index sets.  This is the injectivity behind
"exactly one `(i,j)`": distinct double-peels empty distinct index pairs, hence land on distinct
target configs, so at a fixed target only the matching pair contributes to
`cDownUp_canonical_repr_eq_sum`. -/
theorem idxConfigOf_flatBandSpinConfigList_inj {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    {S S' : Finset (Fin (M + 1))} (hS : S ⊆ I) (hS' : S' ⊆ I)
    (heq : idxConfigOf idx (flatBandSpinConfigList S σ)
      = idxConfigOf idx (flatBandSpinConfigList S' σ)) :
    S = S' := by
  have hmem : ∀ (R : Finset (Fin (M + 1))) (w : Fin (M + 1)) (s : Fin 2),
      (idx w, s) ∈ ((flatBandSpinConfigList R σ).map (fun p => (idx p.1, p.2))).toFinset
        ↔ ∃ z ∈ R, idx z = idx w ∧ σ z = s := by
    intro R w s
    simp only [flatBandSpinConfigList, List.map_map, List.mem_toFinset, List.mem_map,
      Finset.mem_sort, Function.comp]
    constructor
    · rintro ⟨z, hz, he⟩; exact ⟨z, hz, (Prod.ext_iff.mp he).1, (Prod.ext_iff.mp he).2⟩
    · rintro ⟨z, hz, h1, h2⟩; exact ⟨z, hz, by rw [Prod.ext_iff]; exact ⟨h1, h2⟩⟩
  have key : ∀ w ∈ I, ∀ R : Finset (Fin (M + 1)), R ⊆ I →
      (idxConfigOf idx (flatBandSpinConfigList R σ) (idx w, σ w) = 1 ↔ w ∈ R) := by
    intro w hw R hR
    simp only [idxConfigOf]
    rw [if_congr (hmem R w (σ w)) rfl rfl]
    constructor
    · intro h
      by_contra hwR
      rw [if_neg (by rintro ⟨z, hz, h1, _⟩; exact hwR (by
        rwa [flatBandSpecial_idx_injOn hbasis hidx (hR hz) hw h1] at hz))] at h
      exact absurd h (by decide)
    · intro hwR
      rw [if_pos ⟨w, hwR, rfl, rfl⟩]
  ext w
  by_cases hwI : w ∈ I
  · rw [← key w hwI S hS, ← key w hwI S' hS', heq]
  · constructor
    · intro hw; exact absurd (hS hw) hwI
    · intro hw; exact absurd (hS' hw) hwI

/-- **The target config of a canonical double peel determines the removed pair**: if the doubly
erased canonical rest config equals the `(a,b)`-emptied config `idxConfigOf idx (canonical
((I.erase a).erase b) σ)`, with the up-guard on the outer position `i` and the down-guard on the
inner position `j`, then the outer index is `a` and the inner index is `b`.  Rewriting the rest list
by `flatBandSpinConfigList_eraseIdx_eraseIdx`, config injectivity
(`idxConfigOf_flatBandSpinConfigList_inj`) forces the twice-erased index set to match
`(I.erase a).erase b`; `Finset.eq_or_eq_of_erase_erase_eq` (with `erase_right_comm`) pins both
removed indices to `{a,b}`, and the opposite spin guards (`σ = 0` up vs `σ = 1` down) disambiguate
them.  This is the "exactly one `(i,j)`" engine for the `cDownUp_canonical_repr_eq_sum` collapse. -/
theorem flatBandSpinConfig_doublePeel_index_eq {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    {a b : Fin (M + 1)} (hσa : σ a = 0) (hσb : σ b = 1)
    {i : ℕ} (hi : i < (flatBandSpinConfigList I σ).length)
    (hgi : ((flatBandSpinConfigList I σ)[i]).2 = 0) {j : ℕ}
    (hj : j < (flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I σ)[i]).1) σ).length)
    (hgj : ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I σ)[i]).1) σ)[j]).2 = 1)
    (hconfig : idxConfigOf idx (((flatBandSpinConfigList I σ).eraseIdx i).eraseIdx j)
      = idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) :
    ((flatBandSpinConfigList I σ)[i]).1 = a
      ∧ ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I σ)[i]).1) σ)[j]).1 = b := by
  have hcI : ((flatBandSpinConfigList I σ)[i]).1 ∈ I :=
    flatBandSpinConfigList_mem_fst_mem I σ (List.getElem_mem _)
  have hdI : ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I σ)[i]).1) σ)[j]).1 ∈ I :=
    Finset.mem_of_mem_erase (flatBandSpinConfigList_mem_fst_mem _ σ (List.getElem_mem _))
  rw [flatBandSpinConfigList_eraseIdx_eraseIdx I σ hi hj] at hconfig
  have hset : (I.erase ((flatBandSpinConfigList I σ)[i]).1).erase
        ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I σ)[i]).1) σ)[j]).1
      = (I.erase a).erase b :=
    idxConfigOf_flatBandSpinConfigList_inj hbasis hidx σ
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hconfig
  have hσc : σ ((flatBandSpinConfigList I σ)[i]).1 = 0 := by
    rw [← flatBandSpinConfigList_mem_snd_eq I σ (List.getElem_mem hi)]; exact hgi
  have hσd :
      σ ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I σ)[i]).1) σ)[j]).1 = 1 := by
    rw [← flatBandSpinConfigList_mem_snd_eq _ σ (List.getElem_mem hj)]; exact hgj
  have hc := Finset.eq_or_eq_of_erase_erase_eq hcI hset
  rw [Finset.erase_right_comm] at hset
  have hd := Finset.eq_or_eq_of_erase_erase_eq hdI hset
  refine ⟨?_, ?_⟩
  · rcases hc with h | h
    · exact h
    · exfalso; rw [h, hσb] at hσc; exact absurd hσc (by decide)
  · rcases hd with h | h
    · exfalso; rw [h, hσa] at hσd; exact absurd hσd (by decide)
    · exact h

/-- **The target config of a canonical single peel determines the removed index**: for `S ⊆ I`, if
the once-erased canonical rest config equals the `b`-emptied config `idxConfigOf idx (canonical
(S.erase b) σ)` then the erased index `(canonical S σ)[j].1` is `b`.  Rewriting the rest list by
`flatBandSpinConfigList_eraseIdx`, config injectivity forces `S.erase d = S.erase b` (with `d` the
erased index), and since `d ∈ S` this gives `d = b`.  No spin guard is needed: the removed index is
pinned by the config alone.  This is the inner-sum "exactly one `j`" engine. -/
theorem flatBandSpinConfig_singlePeel_index_eq {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    {S : Finset (Fin (M + 1))} (hS : S ⊆ I) {b : Fin (M + 1)}
    {j : ℕ} (hj : j < (flatBandSpinConfigList S σ).length)
    (hconfig : idxConfigOf idx ((flatBandSpinConfigList S σ).eraseIdx j)
      = idxConfigOf idx (flatBandSpinConfigList (S.erase b) σ)) :
    ((flatBandSpinConfigList S σ)[j]).1 = b := by
  have hdS : ((flatBandSpinConfigList S σ)[j]).1 ∈ S :=
    flatBandSpinConfigList_mem_fst_mem S σ (List.getElem_mem _)
  rw [flatBandSpinConfigList_eraseIdx S σ hj] at hconfig
  have hset : S.erase ((flatBandSpinConfigList S σ)[j]).1 = S.erase b :=
    idxConfigOf_flatBandSpinConfigList_inj hbasis hidx σ
      ((Finset.erase_subset _ _).trans hS) ((Finset.erase_subset _ _).trans hS) hconfig
  have hdnot : ((flatBandSpinConfigList S σ)[j]).1 ∉ S.erase b := by
    rw [← hset]; exact Finset.notMem_erase _ _
  by_contra hne
  exact hdnot (Finset.mem_erase.mpr ⟨hne, hdS⟩)

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

end LatticeSystem.Fermion

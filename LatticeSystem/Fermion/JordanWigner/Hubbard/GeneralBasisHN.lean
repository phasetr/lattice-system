import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandFilling
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandOccBasis

/-!
# General basis of the `N`-electron space `H_N` (Tasaki Lemma 9.4)

This file formalizes **Tasaki Lemma 9.4** (Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, Springer 2020, §9.2.3,
pp. 321–322, eq. (9.2.65)/(9.2.66)):

> Let `φ⁽¹⁾, …, φ⁽|Λ|⁾` be `|Λ|` linearly independent single-spin states.
> Then the states
> `|Γ_{S↑,S↓}⟩ = (∏_{j∈S↑} Ĉ†↑(φ⁽ʲ⁾)) (∏_{j∈S↓} Ĉ†↓(φ⁽ʲ⁾)) |Φvac⟩`,
> over all subset pairs `(S↑, S↓)` with `|S↑| + |S↓| = N`, span the
> `N`-electron Hilbert space `H_N`.

We reuse the general-basis Fock-monomial machinery of Tasaki §11.3
(`generalModeMonomial`, `generalOccBasis`, the total-number
diagonalization, and the permutation/sign reordering lemma), which is
already developed for an arbitrary single-particle basis `e`.

## Main results

* `spinfulNElectronSubmodule` — the `N`-electron sector `H_N`, as the
  `(N : ℂ)`-eigenspace of the total number operator.
* `spinfulGeneralBasisState` — Tasaki's `|Γ_{S↑,S↓}⟩` (up creators first,
  then down creators, each set in sorted order).
* `tasaki_lemma_9_4_generalBasis_span` — **Lemma 9.4**, basis-indexed
  form: the `|Γ_{S↑,S↓}⟩` (over `|S↑| + |S↓| = N`) span `H_N`.
* `tasaki_lemma_9_4_of_linearIndependent` — the literal Tasaki phrasing
  for a full linearly independent family `φ`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {M : ℕ}

/-- The `N`-electron sector `H_N` of the spinful Jordan–Wigner space:
the eigenspace of the total number operator at eigenvalue `N`. -/
noncomputable def spinfulNElectronSubmodule (M Ne : ℕ) :
    Submodule ℂ ((Fin (2 * M + 2) → Fin 2) → ℂ) :=
  Module.End.eigenspace (fermionTotalNumber (2 * M + 1)).mulVecLin (Ne : ℂ)

/-- The subset-pair index for Lemma 9.4: pairs `(S↑, S↓)` of orbital
subsets with `|S↑| + |S↓| = N`. The two subsets need **not** be disjoint
(a single orbital may be occupied by both spins). -/
def spinfulSubsetPairIndex (M Ne : ℕ) : Type :=
  {p : Finset (Fin (M + 1)) × Finset (Fin (M + 1)) // p.1.card + p.2.card = Ne}

/-- The up-then-down ordered list of spin-orbital labels for a subset
pair: all `(j, ↑)` for `j ∈ S↑` in sorted order, followed by all `(j, ↓)`
for `j ∈ S↓` in sorted order. -/
def spinfulSubsetPairList (SUp SDown : Finset (Fin (M + 1))) :
    List (Fin (M + 1) × Fin 2) :=
  (SUp.sort (· ≤ ·)).map (fun j => (j, (0 : Fin 2))) ++
    (SDown.sort (· ≤ ·)).map (fun j => (j, (1 : Fin 2)))

/-- Tasaki's `|Γ_{S↑,S↓}⟩` (eq. (9.2.65)): the ordered product of the
up-spin creators (for `j ∈ S↑`) followed by the down-spin creators (for
`j ∈ S↓`), applied to the vacuum. -/
noncomputable def spinfulGeneralBasisState
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (SUp SDown : Finset (Fin (M + 1))) :
    (Fin (2 * M + 2) → Fin 2) → ℂ :=
  generalModeMonomial e (spinfulSubsetPairList SUp SDown)

/-- The length of the subset-pair list is `|S↑| + |S↓|`. -/
theorem spinfulSubsetPairList_length (SUp SDown : Finset (Fin (M + 1))) :
    (spinfulSubsetPairList SUp SDown).length = SUp.card + SDown.card := by
  simp only [spinfulSubsetPairList, List.length_append, List.length_map,
    Finset.length_sort]

/-- Membership in the subset-pair list: `(j, σ)` occurs iff its spin tag
selects the matching subset. -/
theorem mem_spinfulSubsetPairList (SUp SDown : Finset (Fin (M + 1)))
    (q : Fin (M + 1) × Fin 2) :
    q ∈ spinfulSubsetPairList SUp SDown ↔
      (q.2 = 0 ∧ q.1 ∈ SUp) ∨ (q.2 = 1 ∧ q.1 ∈ SDown) := by
  obtain ⟨j, σ⟩ := q
  simp only [spinfulSubsetPairList, List.mem_append, List.mem_map, Finset.mem_sort,
    Prod.mk.injEq]
  fin_cases σ <;> simp

/-- The subset-pair list has no duplicates. -/
theorem spinfulSubsetPairList_nodup (SUp SDown : Finset (Fin (M + 1))) :
    (spinfulSubsetPairList SUp SDown).Nodup := by
  rw [spinfulSubsetPairList]
  apply List.Nodup.append
  · exact (Finset.sort_nodup _ _).map (fun a b h => by simpa using h)
  · exact (Finset.sort_nodup _ _).map (fun a b h => by simpa using h)
  · rw [List.disjoint_left]
    intro q hu hd
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hu
    obtain ⟨b, -, hb⟩ := List.mem_map.mp hd
    have hcontra : (1 : Fin 2) = 0 := congrArg (@Prod.snd (Fin (M + 1)) (Fin 2)) hb
    exact absurd hcontra (by decide)

/-- The up-spin selection of an occupation config. -/
def occUpSet (g : Fin (M + 1) × Fin 2 → Fin 2) : Finset (Fin (M + 1)) :=
  Finset.univ.filter (fun j => g (j, 0) = 1)

/-- The down-spin selection of an occupation config. -/
def occDownSet (g : Fin (M + 1) × Fin 2 → Fin 2) : Finset (Fin (M + 1)) :=
  Finset.univ.filter (fun j => g (j, 1) = 1)

/-- The occupied-mode list of a config is a permutation of the
up-then-down subset list induced by its up/down selections. -/
theorem generalOccFinset_toList_perm (g : Fin (M + 1) × Fin 2 → Fin 2) :
    (generalOccFinset g).toList.Perm
      (spinfulSubsetPairList (occUpSet g) (occDownSet g)) := by
  refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
    (spinfulSubsetPairList_nodup _ _)).mpr (fun q => ?_)
  obtain ⟨j, σ⟩ := q
  rw [Finset.mem_toList, generalOccFinset, Finset.mem_filter,
    mem_spinfulSubsetPairList, occUpSet, occDownSet]
  simp only [Finset.mem_univ, true_and, Finset.mem_filter]
  fin_cases σ <;> simp

/-- The cardinality of the occupied set splits as up- plus down-cardinality. -/
theorem generalOccFinset_card_eq (g : Fin (M + 1) × Fin 2 → Fin 2) :
    (generalOccFinset g).card = (occUpSet g).card + (occDownSet g).card := by
  have h := (generalOccFinset_toList_perm g).length_eq
  rwa [Finset.length_toList, spinfulSubsetPairList_length] at h

/-- The occupation monomial of `g` equals a nonzero multiple of Tasaki's
`|Γ⟩` for the induced subset pair (they differ only by a reordering sign). -/
theorem generalOccMonomial_eq_smul_generalBasisState
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (g : Fin (M + 1) × Fin 2 → Fin 2) :
    ∃ z : ℂ, z ≠ 0 ∧
      generalOccMonomial e g
        = z • spinfulGeneralBasisState e (occUpSet g) (occDownSet g) :=
  generalModeMonomial_perm e (generalOccFinset_toList_perm g)

/-- **Filling coefficient vanishing for an arbitrary basis `e`**: a
number eigenstate `N̂ Φ = D₀ Φ` has vanishing occupation-basis coefficient
on every configuration with a different particle count. (Generalizes the
spectral-eigenbasis version to any `e`; the proof never uses a hopping
matrix.) -/
theorem generalOccBasis_repr_eq_zero_of_card_ne
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} {D₀ : ℕ}
    (hN : (fermionTotalNumber (2 * M + 1)).mulVec Φ = (D₀ : ℂ) • Φ)
    (g : Fin (M + 1) × Fin 2 → Fin 2) (hg : (generalOccFinset g).card ≠ D₀) :
    (generalOccBasis e).repr Φ g = 0 := by
  set b := generalOccBasis e with hb
  have hbcoe : ∀ h, (b h : (Fin (2 * M + 2) → Fin 2) → ℂ) = generalOccMonomial e h :=
    fun h => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) h
  have hexp : (fermionTotalNumber (2 * M + 1)).mulVec Φ
      = ∑ h, (b.repr Φ h * ((generalOccFinset h).card : ℂ)) • (b h) := by
    conv_lhs => rw [← b.sum_repr Φ]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Matrix.mulVec_smul, hbcoe, fermionTotalNumber_mulVec_generalOccMonomial, smul_smul,
      ← hbcoe]
  have hrepr : b.repr ((fermionTotalNumber (2 * M + 1)).mulVec Φ) g
      = b.repr Φ g * ((generalOccFinset g).card : ℂ) := by
    rw [hexp, map_sum]
    simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, b.repr_self]
    rw [Finset.sum_eq_single g]
    · rw [Finsupp.single_eq_same, mul_one]
    · intro h _ hhg
      rw [Finsupp.single_eq_of_ne (Ne.symm hhg), mul_zero]
    · intro h; exact absurd (Finset.mem_univ g) h
  rw [hN, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hrepr
  have hne : ((generalOccFinset g).card : ℂ) - (D₀ : ℂ) ≠ 0 := by
    rw [sub_ne_zero, Ne, Nat.cast_inj]; exact hg
  have hzero : (b.repr Φ g) * (((generalOccFinset g).card : ℂ) - (D₀ : ℂ)) = 0 := by
    rw [mul_sub, ← hrepr]; ring
  exact (mul_eq_zero.mp hzero).resolve_right hne

/-- Each `|Γ_{S↑,S↓}⟩` with `|S↑| + |S↓| = N` lies in the `N`-electron
sector `H_N` (it is a product of `N` creators, so a number eigenstate). -/
theorem spinfulGeneralBasisState_mem
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    {Ne : ℕ} (SUp SDown : Finset (Fin (M + 1)))
    (hcard : SUp.card + SDown.card = Ne) :
    spinfulGeneralBasisState e SUp SDown ∈ spinfulNElectronSubmodule M Ne := by
  rw [spinfulNElectronSubmodule, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
    spinfulGeneralBasisState, fermionTotalNumber_mulVec_generalModeMonomial,
    spinfulSubsetPairList_length, hcard]

/-- **Tasaki Lemma 9.4** (1st ed., Springer 2020, §9.2.3, pp. 321–322,
eq. (9.2.65)), basis-indexed form. For any single-particle basis `e` of
the `M+1` orbitals, the states `|Γ_{S↑,S↓}⟩` over all subset pairs with
`|S↑| + |S↓| = N` span the `N`-electron sector `H_N`. -/
theorem tasaki_lemma_9_4_generalBasis_span
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (Ne : ℕ) :
    Submodule.span ℂ
        (Set.range fun p : spinfulSubsetPairIndex M Ne =>
          spinfulGeneralBasisState e p.1.1 p.1.2)
      = spinfulNElectronSubmodule M Ne := by
  apply le_antisymm
  · -- Each `|Γ⟩` lies in `H_N`.
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact spinfulGeneralBasisState_mem e p.1.1 p.1.2 p.2
  · -- Every `v ∈ H_N` expands over the `N`-card occupation monomials,
    -- each of which is a nonzero multiple of some `|Γ⟩`.
    intro v hv
    rw [spinfulNElectronSubmodule, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv
    have hN : (fermionTotalNumber (2 * M + 1)).mulVec v = (Ne : ℂ) • v := hv
    set b := generalOccBasis e with hb
    have hbcoe : ∀ h, (b h : (Fin (2 * M + 2) → Fin 2) → ℂ) = generalOccMonomial e h :=
      fun h => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) h
    rw [← b.sum_repr v]
    refine Submodule.sum_mem _ (fun g _ => ?_)
    by_cases hcard : (generalOccFinset g).card = Ne
    · -- `g` has the right particle count: its monomial is `z • |Γ⟩`.
      obtain ⟨z, _, hz⟩ := generalOccMonomial_eq_smul_generalBasisState e g
      rw [hbcoe, hz, smul_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine ⟨⟨(occUpSet g, occDownSet g), ?_⟩, rfl⟩
      rw [← generalOccFinset_card_eq]; exact hcard
    · -- Wrong particle count: the coefficient vanishes.
      rw [generalOccBasis_repr_eq_zero_of_card_ne e hN g hcard, zero_smul]
      exact Submodule.zero_mem _

/-- A full linearly independent family of `M+1` single-particle states,
packaged as a basis of `ℂ^{M+1}` (in finite dimension a maximal linearly
independent family is a basis). -/
noncomputable def basisOfFullLinearIndependent
    (φ : Fin (M + 1) → Fin (M + 1) → ℂ) (hφ : LinearIndependent ℂ φ) :
    Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank hφ (by simp)

/-- **Tasaki Lemma 9.4**, literal form for a linearly independent family.
If `φ⁽¹⁾, …, φ⁽ᴹ⁺¹⁾` are linearly independent, the states `|Γ_{S↑,S↓}⟩`
(over `|S↑| + |S↓| = N`) span the `N`-electron sector `H_N`. -/
theorem tasaki_lemma_9_4_of_linearIndependent
    (φ : Fin (M + 1) → Fin (M + 1) → ℂ) (hφ : LinearIndependent ℂ φ) (Ne : ℕ) :
    Submodule.span ℂ
        (Set.range fun p : spinfulSubsetPairIndex M Ne =>
          spinfulGeneralBasisState (basisOfFullLinearIndependent φ hφ) p.1.1 p.1.2)
      = spinfulNElectronSubmodule M Ne :=
  tasaki_lemma_9_4_generalBasis_span _ Ne

end LatticeSystem.Fermion

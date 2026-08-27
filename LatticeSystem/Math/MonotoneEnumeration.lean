import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Monotone re-enumerations of a finite family and their lowest levels

A family `g : Fin m → α` presented in an arbitrary order and a monotone family `ε : Fin m → α`
carrying the same multiset of values are the same data listed differently: `ε` is `g` read along
the sorting permutation of `g`.  This module records that bridge and the consequences an
application needs once it has replaced `g` by its increasing enumeration `ε`:

* **the fractional knapsack bound**: the sum of the `k` lowest levels
  `∑ i : Fin k, ε (Fin.castLE hk i)` is a lower bound for *every* weighted sum `∑ j, ε j * w j`
  whose weights satisfy `0 ≤ w j ≤ 1` and `∑ j, w j = k` — the weights need not be `{0, 1}`-valued,
  so a fractional occupation of the levels cannot beat filling the lowest ones;
* the same bound read against the unsorted family `g`;
* some `k`-element subset of the index type attains the sum of the `k` lowest levels;
* the sum of the `k + 1` lowest levels splits as the sum of the `k` lowest plus the level `ε ⟨k, _⟩`
  sitting on top of them.

The sorting bridge and the two `Finset`-level statements are given for an abstract linearly ordered
`α`, with the order-theoretic content coming from `Tuple.sort` (mathlib's increasing enumeration of
a tuple).  The weighted bounds are stated over `ℝ`, where the fractional weights live.
-/

namespace LatticeSystem.Math

/-- **A monotone re-enumeration is the sorted family**: if `ε` is monotone and carries the same
multiset of values as `g`, then `ε = g ∘ Tuple.sort g`.

This is not `Tuple.unique_monotone`, which compares two *permutations of one and the same* tuple;
here `ε` and `g` are unrelated families tied only by the multiset equality `hspec`.  The proof
nevertheless reuses the chain by which mathlib proves that lemma, after turning `hspec` into a
permutation of the underlying lists. -/
theorem eq_comp_sort_of_monotone_of_map_eq {α : Type*} [LinearOrder α] {m : ℕ}
    {ε g : Fin m → α} (hmono : Monotone ε)
    (hspec : (Finset.univ : Finset (Fin m)).val.map ε
      = (Finset.univ : Finset (Fin m)).val.map g) :
    ε = g ∘ Tuple.sort g := by
  rw [Fin.univ_val_map, Fin.univ_val_map] at hspec
  have hperm : (List.ofFn ε).Perm (List.ofFn (g ∘ Tuple.sort g)) :=
    (Multiset.coe_eq_coe.mp hspec).trans ((Tuple.sort g).ofFn_comp_perm g).symm
  exact List.ofFn_injective (hperm.eq_of_pairwise' hmono.sortedLE_ofFn.pairwise
    (Tuple.monotone_sort g).sortedLE_ofFn.pairwise)

/-- **The fractional knapsack bound for a monotone family**: for monotone `ε : Fin m → ℝ` and
weights `w` with `0 ≤ w j ≤ 1` and `∑ j, w j = k`, the sum of the `k` lowest levels is a lower
bound for the weighted sum: `∑ i : Fin k, ε (Fin.castLE hk i) ≤ ∑ j, ε j * w j`.

The weights are *not* assumed `{0, 1}`-valued, so this covers a fractional occupation of the levels
as well as the choice of a `k`-element subset.

Writing `T` for the first `k` indices, `χ` for its indicator and `θ` for the top level `ε ⟨k-1, _⟩`
of `T`, every term of `∑ j, (ε j − θ)(w j − χ j)` is nonnegative: inside `T` both factors are
nonpositive (`ε j ≤ θ` by monotonicity and `w j ≤ 1 = χ j`), outside `T` both are nonnegative.
Since `∑ j, w j = k = ∑ j, χ j`, the `θ`-terms cancel and the sum collapses to
`∑ j, ε j * w j − ∑ i : Fin k, ε (Fin.castLE hk i)`. -/
theorem sum_lowestLevels_le_sum_weighted {m k : ℕ} (hk : k ≤ m) {ε : Fin m → ℝ}
    (hmono : Monotone ε) {w : Fin m → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1)
    (hsum : ∑ j, w j = (k : ℝ)) :
    ∑ i : Fin k, ε (Fin.castLE hk i) ≤ ∑ j, ε j * w j := by
  classical
  cases k with
  | zero =>
      have hzero : ∀ j : Fin m, w j = 0 :=
        fun j => (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw0 j).mp
          (by rw [hsum]; norm_num) j (Finset.mem_univ j)
      rw [Fin.sum_univ_zero]
      exact Finset.sum_nonneg fun j _ => by rw [hzero j, mul_zero]
  | succ k' =>
      set T : Finset (Fin m) := Finset.univ.map ⟨Fin.castLE hk, Fin.castLE_injective hk⟩ with hTdef
      set χ : Fin m → ℝ := fun j => if j ∈ T then 1 else 0 with hχdef
      have hmemT : ∀ j : Fin m, j ∈ T ↔ (j : ℕ) < k' + 1 := by
        intro j
        rw [hTdef, Finset.mem_map]
        constructor
        · rintro ⟨i, -, hi⟩
          rw [← hi]
          exact i.isLt
        · intro hj
          exact ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩
      have hterm : ∀ j : Fin m, 0 ≤ (ε j - ε (⟨k', hk⟩ : Fin m)) * (w j - χ j) := by
        intro j
        by_cases hj : j ∈ T
        · have hle : ε j - ε (⟨k', hk⟩ : Fin m) ≤ 0 :=
            sub_nonpos.mpr (hmono (Fin.le_def.mpr (Nat.lt_succ_iff.mp ((hmemT j).mp hj))))
          have hχ1 : χ j = 1 := by rw [hχdef]; simp [hj]
          have hwle : w j - χ j ≤ 0 := by rw [hχ1]; linarith [hw1 j]
          have hprod := mul_nonneg (neg_nonneg.mpr hle) (neg_nonneg.mpr hwle)
          rwa [neg_mul_neg] at hprod
        · have hge : 0 ≤ ε j - ε (⟨k', hk⟩ : Fin m) :=
            sub_nonneg.mpr (hmono (Fin.le_def.mpr
              (Nat.le_of_succ_le (Nat.not_lt.mp fun hc => hj ((hmemT j).mpr hc)))))
          have hχ0 : χ j = 0 := by rw [hχdef]; simp [hj]
          have hwge : 0 ≤ w j - χ j := by rw [hχ0]; linarith [hw0 j]
          exact mul_nonneg hge hwge
      have hsumχ : ∑ j, χ j = ((k' + 1 : ℕ) : ℝ) := by
        rw [hχdef]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hTdef, Finset.card_map,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      have hsumεχ : ∑ j, ε j * χ j = ∑ i : Fin (k' + 1), ε (Fin.castLE hk i) := by
        rw [hχdef]
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_mem, Finset.univ_inter, hTdef, Finset.sum_map]
        rfl
      have hexpand : ∑ j, (ε j - ε (⟨k', hk⟩ : Fin m)) * (w j - χ j)
          = (∑ j, ε j * w j) - ∑ i : Fin (k' + 1), ε (Fin.castLE hk i) := by
        calc ∑ j, (ε j - ε (⟨k', hk⟩ : Fin m)) * (w j - χ j)
            = ∑ j : Fin m, ((ε j * w j - ε j * χ j)
                + (ε (⟨k', hk⟩ : Fin m) * χ j - ε (⟨k', hk⟩ : Fin m) * w j)) :=
              Finset.sum_congr rfl fun j _ => by ring
          _ = ((∑ j, ε j * w j) - ∑ j, ε j * χ j)
                + ((∑ j : Fin m, ε (⟨k', hk⟩ : Fin m) * χ j)
                  - ∑ j : Fin m, ε (⟨k', hk⟩ : Fin m) * w j) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          _ = (∑ j, ε j * w j) - ∑ i : Fin (k' + 1), ε (Fin.castLE hk i) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, hsumχ, hsumεχ]
              ring
      have hkey : 0 ≤ ∑ j, (ε j - ε (⟨k', hk⟩ : Fin m)) * (w j - χ j) :=
        Finset.sum_nonneg fun j _ => hterm j
      rw [hexpand] at hkey
      linarith

/-- **The fractional knapsack bound against the unsorted family**: if `ε` is monotone and carries
the same multiset of values as `g`, then for weights `w` with `0 ≤ w j ≤ 1` and `∑ j, w j = k`,
`∑ i : Fin k, ε (Fin.castLE hk i) ≤ ∑ j, g j * w j`.

Transporting the weights along the sorting permutation of `g` turns the right-hand sum into a
weighted sum of `ε`, where `sum_lowestLevels_le_sum_weighted` applies. -/
theorem sum_lowestLevels_le_sum_weighted_of_map_eq {m k : ℕ} (hk : k ≤ m) {ε g : Fin m → ℝ}
    (hmono : Monotone ε)
    (hspec : (Finset.univ : Finset (Fin m)).val.map ε
      = (Finset.univ : Finset (Fin m)).val.map g)
    {w : Fin m → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1)
    (hsum : ∑ j, w j = (k : ℝ)) :
    ∑ i : Fin k, ε (Fin.castLE hk i) ≤ ∑ j, g j * w j := by
  have hε := eq_comp_sort_of_monotone_of_map_eq hmono hspec
  have hsum' : ∑ j, w (Tuple.sort g j) = (k : ℝ) := by
    rw [Equiv.sum_comp (Tuple.sort g) w, hsum]
  have hbound := sum_lowestLevels_le_sum_weighted hk hmono
    (w := fun j => w (Tuple.sort g j)) (fun j => hw0 _) (fun j => hw1 _) hsum'
  have hgw : ∑ j, ε j * w (Tuple.sort g j) = ∑ j, g j * w j := by
    rw [hε]
    exact Equiv.sum_comp (Tuple.sort g) fun j => g j * w j
  rwa [hgw] at hbound

/-- **The lowest levels are attained by an explicit subset**: if `ε` is monotone and carries the
same multiset of values as `g`, some `k`-element subset `S` of the index type satisfies
`∑ p ∈ S, g p = ∑ i : Fin k, ε (Fin.castLE hk i)`.

The witness is the image under the sorting permutation of `g` of the first `k` indices. -/
theorem exists_lowestLevels_finset_of_map_eq {α : Type*} [LinearOrder α] [AddCommMonoid α]
    {m k : ℕ} (hk : k ≤ m) {ε g : Fin m → α} (hmono : Monotone ε)
    (hspec : (Finset.univ : Finset (Fin m)).val.map ε
      = (Finset.univ : Finset (Fin m)).val.map g) :
    ∃ S : Finset (Fin m), S.card = k ∧ ∑ p ∈ S, g p = ∑ i : Fin k, ε (Fin.castLE hk i) := by
  classical
  have hε := eq_comp_sort_of_monotone_of_map_eq hmono hspec
  refine ⟨Finset.univ.map ⟨fun i : Fin k => Tuple.sort g (Fin.castLE hk i), ?_⟩, ?_, ?_⟩
  · exact (Equiv.injective _).comp (Fin.castLE_injective hk)
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hε]
    rfl

/-- **Splitting off the top of the lowest levels**: the sum of the `k + 1` lowest levels is the sum
of the `k` lowest levels plus the level `ε ⟨k, hk⟩` sitting immediately above them. -/
theorem sum_lowestLevels_succ {α : Type*} [AddCommMonoid α] {m k : ℕ} (hk : k + 1 ≤ m)
    {ε : Fin m → α} :
    ∑ i : Fin (k + 1), ε (Fin.castLE hk i)
      = (∑ i : Fin k, ε (Fin.castLE (Nat.le_of_succ_le hk) i)) + ε ⟨k, hk⟩ := by
  rw [Fin.sum_univ_castSucc]
  rfl

end LatticeSystem.Math

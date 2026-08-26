import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Monotone re-enumerations of a finite family and their lowest levels

A family `g : Fin m → α` presented in an arbitrary order and a monotone family `ε : Fin m → α`
carrying the same multiset of values are the same data listed differently: `ε` is `g` read along
the sorting permutation of `g`.  This module records that bridge and the three consequences an
application needs once it has replaced `g` by its increasing enumeration `ε`:

* the sum of the `k` lowest levels `∑ i : Fin k, ε (Fin.castLE hk i)` is a lower bound for the sum
  of `g` over *any* `k`-element subset of the index type;
* some `k`-element subset attains that lower bound;
* the sum of the `k + 1` lowest levels splits as the sum of the `k` lowest plus the level `ε ⟨k, _⟩`
  sitting on top of them.

Everything is stated for an abstract linearly ordered `α`; the order-theoretic content comes from
`Tuple.sort` (mathlib's increasing enumeration of a tuple) and `Finset.orderEmbOfFin` (mathlib's
increasing enumeration of a finite set).
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

/-- **A strictly monotone map between index types does not decrease the index**: for
`f : Fin k → Fin m` strictly monotone, `i ≤ f i` as natural numbers. -/
private theorem val_le_val_of_strictMono {k m : ℕ} {f : Fin k → Fin m} (hf : StrictMono f)
    (i : Fin k) : (i : ℕ) ≤ (f i : ℕ) := by
  obtain ⟨j, hj⟩ := i
  induction j with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hn : n < k := Nat.lt_of_succ_lt hj
      have hstep : f ⟨n, hn⟩ < f ⟨n + 1, hj⟩ := hf (by simp [Fin.lt_def])
      -- The conclusion `n < (f ⟨n + 1, hj⟩ : ℕ)` matches the goal only up to unfolding
      -- `Nat.lt` and the `Fin.val` projection of the literal index.
      exact Nat.lt_of_le_of_lt (ih hn) (Fin.lt_def.mp hstep)

/-- **The lowest levels of a monotone family minimise the sum**: for monotone `ε` and any
`k`-element subset `T` of the index type, `∑ i : Fin k, ε (Fin.castLE hk i) ≤ ∑ p ∈ T, ε p`.

Enumerating `T` in increasing order, its `i`-th smallest element has index at least `i`, so
monotonicity compares the two sums term by term. -/
theorem sum_lowestLevels_le_sum_of_monotone {α : Type*} [LinearOrder α] [AddCommMonoid α]
    [IsOrderedAddMonoid α] {m k : ℕ} (hk : k ≤ m) {ε : Fin m → α} (hmono : Monotone ε)
    {T : Finset (Fin m)} (hT : T.card = k) :
    ∑ i : Fin k, ε (Fin.castLE hk i) ≤ ∑ p ∈ T, ε p := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ T hT]
  rw [Finset.sum_map]
  refine Finset.sum_le_sum fun i _ => hmono ?_
  exact Fin.le_def.mpr (by
    simpa using val_le_val_of_strictMono (T.orderEmbOfFin hT).strictMono i)

/-- **The lowest levels bound the sum over any `k`-element subset of the unsorted family**: if `ε`
is monotone and carries the same multiset of values as `g`, then for every `k`-element subset `S`
of the index type, `∑ i : Fin k, ε (Fin.castLE hk i) ≤ ∑ p ∈ S, g p`.

Transporting `S` along the sorting permutation of `g` turns the right-hand sum into a sum of `ε`
over a `k`-element subset, where `sum_lowestLevels_le_sum_of_monotone` applies. -/
theorem sum_lowestLevels_le_sum_of_map_eq {α : Type*} [LinearOrder α] [AddCommMonoid α]
    [IsOrderedAddMonoid α] {m k : ℕ} (hk : k ≤ m) {ε g : Fin m → α} (hmono : Monotone ε)
    (hspec : (Finset.univ : Finset (Fin m)).val.map ε
      = (Finset.univ : Finset (Fin m)).val.map g)
    {S : Finset (Fin m)} (hS : S.card = k) :
    ∑ i : Fin k, ε (Fin.castLE hk i) ≤ ∑ p ∈ S, g p := by
  classical
  have hε := eq_comp_sort_of_monotone_of_map_eq hmono hspec
  set T : Finset (Fin m) := S.map (Tuple.sort g).symm.toEmbedding with hTdef
  have hTcard : T.card = k := by rw [hTdef, Finset.card_map, hS]
  have hmap : T.map (Tuple.sort g).toEmbedding = S := by
    rw [hTdef, Finset.map_map]
    convert Finset.map_refl
    ext x
    simp
  have hsum : ∑ p ∈ S, g p = ∑ j ∈ T, ε j := by
    rw [← hmap, Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hε]
    rfl
  rw [hsum]
  exact sum_lowestLevels_le_sum_of_monotone hk hmono hTcard

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

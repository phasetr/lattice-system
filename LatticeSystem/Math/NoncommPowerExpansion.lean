import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn

/-!
# Noncommutative multinomial expansion of a smul-linear combination

This module proves the **noncommutative multinomial theorem** for an `M`-th power of a finite
`ℂ`-linear combination `∑ α, c α • O α` of operators `O α` in a (possibly noncommutative)
`ℂ`-algebra `A`:

`(∑ α, c α • O α) ^ M = ∑ f : Fin M → ι, (∏ j, c (f j)) • (List.ofFn fun j => O (f j)).prod`.

The ordered operator product is kept **literally** as `(List.ofFn …).prod`, so operator order is
fully preserved (no commutators are introduced).  Mathlib's `Finset.sum_pow'` is `CommSemiring`-only
and cannot be used here, so the expansion is proved from scratch by induction on `M` using the
`Fin.snoc` reindexing of `Fin (M + 1) → ι`.

It also records the elementary count-reindexing `prod_comp_eq_prod_pow_card`
(`∏ j, c (f j) = ∏ α, c α ^ #{j | f j = α}`) used to collapse each monomial coefficient into a
multiplicity-indexed product.

These are consumed by the operator polynomial expansion of the Anderson-tower sphere average
(Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, GTP), §4.2.2,
eq. (4.2.58), p.108).
-/

open scoped BigOperators

namespace LatticeSystem.Math

/-- The `Fin.snoc` bijection `(Fin M → ι) × ι ≃ (Fin (M + 1) → ι)` sending `(f, α)` to the extended
tuple `Fin.snoc f α`.  Its inverse splits a tuple into its initial segment and its last entry. -/
def finSnocEquiv (M : ℕ) (ι : Type*) : (Fin M → ι) × ι ≃ (Fin (M + 1) → ι) where
  toFun p := Fin.snoc p.1 p.2
  invFun g := (Fin.init g, g (Fin.last M))
  left_inv p := by simp [Fin.init_snoc, Fin.snoc_last]
  right_inv g := by simp [Fin.snoc_init_self]

/-- **Noncommutative multinomial expansion.**  For scalars `c : ι → ℂ` and operators `O : ι → A` in
a `ℂ`-algebra `A`, the `M`-th power of the smul-linear combination `∑ α, c α • O α` expands as a sum
over index tuples `f : Fin M → ι`, each contributing the scalar product `∏ j, c (f j)` times the
**ordered** operator product `(List.ofFn fun j => O (f j)).prod`.  Operator order is preserved
exactly (no commutators). **Note**: this is a generalization of `add_pow_eq_sum_ofFn`
(OrderOperatorAlgebra.lean, line 619), which specializes to `ι = Bool` (binary choice). -/
theorem pow_sum_smul_eq_sum_smul_prod {ι A : Type*} [Fintype ι]
    [Ring A] [Algebra ℂ A] (c : ι → ℂ) (O : ι → A) (M : ℕ) :
    (∑ α, c α • O α) ^ M
      = ∑ f : Fin M → ι, (∏ j, c (f j)) • (List.ofFn fun j => O (f j)).prod := by
  induction M with
  | zero =>
    rw [pow_zero, Fintype.sum_unique]
    simp
  | succ M ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (finSnocEquiv M ι)
      (fun g => (∏ j, c (g j)) • (List.ofFn fun j => O (g j)).prod), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun α _ => ?_
    simp only [finSnocEquiv, Equiv.coe_fn_mk]
    rw [smul_mul_smul_comm]
    congr 1
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    · rw [List.ofFn_succ', List.prod_concat]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- **Count reindexing.**  For a commutative monoid `M`, a scalar family `c : ι → M` over a finite
index and a tuple `f : Fin n → ι`, the product `∏ j, c (f j)` equals the product over `ι` of `c α`
raised to the multiplicity `#{j | f j = α}` of `α` in `f`. -/
theorem prod_comp_eq_prod_pow_card {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    {n : ℕ} (c : ι → M) (f : Fin n → ι) :
    ∏ j, c (f j) = ∏ α, c α ^ (Finset.univ.filter (fun j => f j = α)).card := by
  rw [Finset.prod_comp c f]
  refine Finset.prod_subset (Finset.subset_univ _) fun α _ hα => ?_
  rw [Finset.mem_image] at hα
  have hempty : Finset.univ.filter (fun j => f j = α) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact fun j _ hj => hα ⟨j, Finset.mem_univ j, hj⟩
  rw [hempty, Finset.card_empty, pow_zero]

end LatticeSystem.Math

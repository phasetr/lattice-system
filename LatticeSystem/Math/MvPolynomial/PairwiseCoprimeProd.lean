/-
Two generic combinatorial lemmas about finite products, used by the degree-counting step of the
AKLT ground-state uniqueness proof (Tasaki §7.1.3, Kennedy–Lieb–Tasaki [41]).

* `prod_dvd_of_pairwise_isRelPrime` — in a `DecompositionMonoid` (e.g. a UFD such as
  `MvPolynomial σ ℂ`), if each factor `f i` divides `m` and the factors are pairwise relatively
  prime, then their finite product divides `m`.  Mathlib has the `IsCoprime` (Bézout) analogue
  `Finset.prod_dvd_of_coprime`, but the AKLT argument lives in the non-Bézout ring
  `MvPolynomial (Fin L × Fin 2) ℂ`, where only the weaker `IsRelPrime` is available; this lemma
  bundles `IsRelPrime.prod_right` with `IsRelPrime.mul_dvd` by induction on the index set.
* `totalDegree_prod_of_isDomain` — over an integral domain the total degree of a finite product of
  nonzero multivariate polynomials is the sum of the total degrees (mathlib only provides the
  inequality `totalDegree_multiset_prod`).  Applied to the `L` bond factors it gives
  `totalDegree (∏ f_x) = 2L`, the degree count forcing one-dimensionality in Tasaki eq. (7.1.25).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, 2020),
§7.1.3 "The Uniqueness of the Ground State", pp. 186–188, eq. (7.1.25).
-/
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Degrees

open MvPolynomial

namespace LatticeSystem.Math

/-- **Pairwise-coprime finite product divides.**  In a `DecompositionMonoid` (any UFD qualifies),
if every factor `f i` (`i ∈ s`) divides `m` and the factors are pairwise relatively prime, then the
product `∏ i ∈ s, f i` divides `m`.  This is the `IsRelPrime` counterpart of the Bézout lemma
`Finset.prod_dvd_of_coprime`, obtained by induction: `IsRelPrime.prod_right` makes `f a` relatively
prime to the rest of the product and `IsRelPrime.mul_dvd` combines the two divisibilities. -/
theorem prod_dvd_of_pairwise_isRelPrime {ι : Type*} {M : Type*}
    [CommMonoidWithZero M] [DecompositionMonoid M] (s : Finset ι) (f : ι → M) (m : M)
    (hd : ∀ i ∈ s, f i ∣ m)
    (hc : (↑s : Set ι).Pairwise (fun i j => IsRelPrime (f i) (f j))) :
    (∏ i ∈ s, f i) ∣ m := by
  classical
  revert hd hc
  refine Finset.induction_on s ?_ ?_
  · intro _ _; simp
  · intro a t ha ih hd hc
    rw [Finset.prod_insert ha]
    refine IsRelPrime.mul_dvd ?_ (hd a (Finset.mem_insert_self a t)) ?_
    · refine IsRelPrime.prod_right fun i hi => ?_
      exact hc (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi)
        (by rintro rfl; exact ha hi)
    · exact ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))
        (hc.mono (Finset.coe_subset.mpr (Finset.subset_insert a t)))

/-- **Total degree of a finite product over a domain.**  Over an integral domain the total degree
of a product of nonzero multivariate polynomials is the sum of the individual total degrees.
Mathlib only supplies the inequality `totalDegree_multiset_prod`; the equality follows by induction
from `totalDegree_mul_of_isDomain` (each partial product stays nonzero by
`Finset.prod_ne_zero_iff`).  Used to compute `totalDegree (∏_x f_x) = 2L` in Tasaki eq. (7.1.25). -/
theorem totalDegree_prod_of_isDomain {ι σ R : Type*} [CommRing R] [IsDomain R]
    (s : Finset ι) (f : ι → MvPolynomial σ R) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _; simp [totalDegree_one]
  · intro a t ha ih hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      totalDegree_mul_of_isDomain (hf a (Finset.mem_insert_self a t))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end LatticeSystem.Math

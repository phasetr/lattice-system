/-
Per-site (weighted homogeneous) grading of the Weyl polynomial representation.

The total-degree grading of `LatticeSystem.Math.MvPolynomial.WeylSpinOneMap`
(`weylMap_isHomogeneous`: every Weyl image is homogeneous of total degree `2L`) is too coarse to
control the cofactor of the bond product `∏_x f_x`: a cofactor of total degree `2` in the `2L`
Weyl variables still ranges over a large space.  The finer grading that does control it assigns to
each variable its **own site**, so that a polynomial carries one degree per site of the chain;
the Weyl image then has degree `2` at every site, and a cofactor of the bond product is pinned to
the monomials of degree `1` at the two chain ends and `0` at every interior site.

This file provides that layer in two parts.

* A generic graded pair over an arbitrary (left-cancellative) weight monoid `M`:
  `weightedHomogeneousComponent_mul_of_isWeightedHomogeneous` (the weighted component of a product
  whose left factor is homogeneous) and the resulting cofactor lemma
  `isWeightedHomogeneous_cofactor_weight`.  Mathlib has `IsWeightedHomogeneous.mul` / `.prod` but
  no quotient (cofactor) counterpart.  Left cancellation in `M` is what turns "the `b`-side
  selector `weight b = m`" into "the `d`-side selector `weight d = k + m`"; it holds for the two
  weight monoids used here (`ℕ` and `Fin L →₀ ℕ`).
* The instances that specialise that pair to the Weyl representation of the spin-`1` chain: the
  per-site weight `siteWeight` on the Weyl variables `Fin L × Fin 2`, valued in the per-site degree
  monoid `Fin L →₀ ℕ`; the per-site homogeneity `weylMap_isWeightedHomogeneous` of the Weyl image;
  and the weighted homogeneity `bondFactor_isWeightedHomogeneous` of the bilinear bond factor.

The cofactor lemma is **false without `q ≠ 0`**: the zero polynomial is weighted homogeneous of
every degree, so both homogeneity hypotheses become vacuous while the conclusion is arbitrary.
The counterexample is kept as the regression test
`LatticeSystem.Tests.GradedPolynomialLayerNegativeControl`.

The two gradings are not independent: `weylMap_isWeightedHomogeneous` (degree `2` at each site)
implies `weylMap_isHomogeneous` (total degree `2L`), by summing the per-site degrees, i.e. by
applying `Finsupp.weight (fun _ => 1)` to the per-site degree identity.  The converse fails, since
a fixed total degree does not pin the degree at each individual site.  The total-degree statement
is nevertheless kept as it stands, because it is the form directly consumed by
`LatticeSystem.Quantum.SpinS.AKLTUniqueness.ProductBondDivisibility`, which compares total degrees
of the bond product and the Weyl image.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, 2020),
§7.1.3 "The Uniqueness of the Ground State", pp. 186–188, eqs. (7.1.22)–(7.1.25); polynomial
representation due to Arovas–Auerbach–Haldane [10]; proof due to Kennedy–Lieb–Tasaki [41].
-/
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import LatticeSystem.Math.MvPolynomial.WeylSpinOneMap
import LatticeSystem.Math.MvPolynomial.BilinearFactorCoprime

open MvPolynomial

namespace LatticeSystem.Math

section GradedRing

variable {σ M : Type*} [AddCommMonoid M] [IsLeftCancelAdd M] {w : σ → M}

/-- The weighted homogeneous component of a product with a homogeneous left factor: if `q` is
`w`-homogeneous of weighted degree `k`, then the degree-`(k + m)` component of `q * r` is `q`
times the degree-`m` component of `r`.  Proved coefficientwise on `Finset.antidiagonal`: for a
pair `(a, b)` with `coeff a q ≠ 0` one has `weight a = k`, so `weight (a + b) = k + m` and
`weight b = m` are equivalent by left cancellation in `M`. -/
theorem weightedHomogeneousComponent_mul_of_isWeightedHomogeneous {q : MvPolynomial σ ℂ} {k : M}
    (hq : q.IsWeightedHomogeneous w k) (r : MvPolynomial σ ℂ) (m : M) :
    weightedHomogeneousComponent w (k + m) (q * r) = q * weightedHomogeneousComponent w m r := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul]
  by_cases hd : Finsupp.weight w d = k + m
  · rw [if_pos hd, coeff_mul]
    refine Finset.sum_congr rfl ?_
    rintro ⟨a, b⟩ hab
    rw [coeff_weightedHomogeneousComponent]
    by_cases ha : coeff a q = 0
    · simp [ha]
    · have hsum : Finsupp.weight w a + Finsupp.weight w b = k + m := by
        rw [← map_add, Finset.mem_antidiagonal.mp hab, hd]
      rw [hq ha] at hsum
      rw [if_pos (add_left_cancel hsum)]
  · rw [if_neg hd, coeff_mul]
    refine (Finset.sum_eq_zero ?_).symm
    rintro ⟨a, b⟩ hab
    rw [coeff_weightedHomogeneousComponent]
    by_cases ha : coeff a q = 0
    · simp [ha]
    · have hb : Finsupp.weight w b ≠ m := fun hb =>
        hd (by rw [← Finset.mem_antidiagonal.mp hab, map_add, hq ha, hb])
      rw [if_neg hb, mul_zero]

/-- **Cofactor lemma.**  If `q` is `w`-homogeneous of weighted degree `k` and nonzero, and the
product `q * r` is `w`-homogeneous of weighted degree `n`, then every monomial `d` occurring in
`r` has `k + weight w d = n` (i.e. `r` is `w`-homogeneous of the complementary degree).

The hypothesis `q ≠ 0` is load-bearing: for `q = 0` both homogeneity hypotheses hold vacuously
for arbitrary `k` and `n` (regression test `GradedPolynomialLayerNegativeControl`).  The proof
uses it through `mul_ne_zero`: the degree-`weight w d` component of `r` is nonzero (its
`d`-coefficient is `coeff d r ≠ 0`), hence so is `q *` that component, which by
`weightedHomogeneousComponent_mul_of_isWeightedHomogeneous` is the degree-`(k + weight w d)`
component of `q * r`. -/
theorem isWeightedHomogeneous_cofactor_weight {q r : MvPolynomial σ ℂ} {k n : M}
    (hq : q.IsWeightedHomogeneous w k) (hq0 : q ≠ 0)
    (hqr : (q * r).IsWeightedHomogeneous w n) {d : σ →₀ ℕ} (hd : d ∈ r.support) :
    k + Finsupp.weight w d = n := by
  classical
  set m := Finsupp.weight w d with hm
  have hcoeff : coeff d (weightedHomogeneousComponent w m r) = coeff d r := by
    rw [coeff_weightedHomogeneousComponent, if_pos hm.symm]
  have hcomp : weightedHomogeneousComponent w m r ≠ 0 := fun h =>
    mem_support_iff.mp hd (by rw [← hcoeff, h, coeff_zero])
  by_contra hne
  refine mul_ne_zero hq0 hcomp ?_
  rw [← weightedHomogeneousComponent_mul_of_isWeightedHomogeneous hq r m]
  exact hqr.weightedHomogeneousComponent_ne (k + m) hne

end GradedRing

/-- The bilinear bond factor `X a * X b - X c * X d` is `w`-homogeneous of weighted degree
`w a + w b` whenever its two monomials carry the same weight (`w a + w b = w c + w d`); this is
the weighted counterpart of `bondFactor_totalDegree`. -/
theorem bondFactor_isWeightedHomogeneous {σ M : Type*} [AddCommMonoid M] (w : σ → M)
    (a b c d : σ) (h : w a + w b = w c + w d) :
    (bondFactor a b c d).IsWeightedHomogeneous w (w a + w b) := by
  have hab : (X a * X b : MvPolynomial σ ℂ).IsWeightedHomogeneous w (w a + w b) :=
    (isWeightedHomogeneous_X ℂ w a).mul (isWeightedHomogeneous_X ℂ w b)
  have hcd : (X c * X d : MvPolynomial σ ℂ).IsWeightedHomogeneous w (w a + w b) := by
    rw [h]
    exact (isWeightedHomogeneous_X ℂ w c).mul (isWeightedHomogeneous_X ℂ w d)
  exact (weightedHomogeneousSubmodule ℂ w (w a + w b)).sub_mem hab hcd

variable {L : ℕ}

/-- The per-site weight of the Weyl variables: both variables `u_x = (x,0)` and `v_x = (x,1)` of
site `x` have weight `Finsupp.single x 1`, the basis vector of `x` in the per-site degree monoid
`Fin L →₀ ℕ`.  A polynomial is then `siteWeight`-homogeneous exactly when all its monomials have
the same degree *at every site separately*, which is strictly finer than the total-degree grading
used by `weylMap_isHomogeneous`. -/
noncomputable def siteWeight : Fin L × Fin 2 → (Fin L →₀ ℕ) := fun e => Finsupp.single e.1 1

/-- **Per-site weights are plain exponent sums.**  Evaluating the `siteWeight`-weight of a
multidegree `d` at a single site `y` returns the total exponent `d (y,0) + d (y,1)` of that site's
two Weyl variables.  This is the bridge that turns the `Finsupp`-valued weighted grading into
ordinary arithmetic on exponents, and it is what lets the cofactor lemma be read site by site. -/
theorem weight_siteWeight_apply (d : (Fin L × Fin 2) →₀ ℕ) (y : Fin L) :
    (Finsupp.weight (siteWeight (L := L)) d) y = d (y, 0) + d (y, 1) := by
  classical
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype d (fun i c => c • siteWeight i) (fun i => zero_smul ℕ (siteWeight i)),
    Finsupp.finset_sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single y]
  · simp [siteWeight, Fin.sum_univ_two]
  · intro x _ hxy
    simp [siteWeight, hxy]
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- The per-site degree `∑_x single x 2` of a Weyl image evaluates to `2` at every site: each
spin-`1` site contributes exactly one degree-`2` binary form (Tasaki eq. (7.1.22)). -/
theorem weylMapWeight_apply (y : Fin L) :
    (∑ x : Fin L, Finsupp.single x 2 : Fin L →₀ ℕ) y = 2 := by
  classical
  rw [Finsupp.finset_sum_apply]
  simp

/-- Each single-site multidegree has per-site weight `Finsupp.single x 2`: site `x` carries
degree `2` (Tasaki eq. (7.1.22): one spin-`1` site is one degree-`2` binary form) and every other
site carries degree `0`. -/
theorem weight_siteWeight_mdSite (x : Fin L) (k : Fin 3) :
    Finsupp.weight (siteWeight (L := L)) (mdSite x k) = Finsupp.single x 2 := by
  fin_cases k <;>
    simp [mdSite, siteWeight, map_add, Finsupp.weight_single, Finsupp.smul_single,
      ← Finsupp.single_add]

/-- The multidegree of a chain state has per-site weight `∑_x single x 2`: every site carries
degree exactly `2` (the per-site refinement of `md_degree`, which only records the total `2L`). -/
theorem weight_siteWeight_md (σ : Fin L → Fin 3) :
    Finsupp.weight (siteWeight (L := L)) (md σ) = ∑ x : Fin L, Finsupp.single x 2 := by
  rw [md, map_sum]
  exact Finset.sum_congr rfl fun x _ => weight_siteWeight_mdSite x (σ x)

/-- **Per-site refinement of `weylMap_isHomogeneous`.**  The Weyl image `weylMap Φ` is
`siteWeight`-homogeneous of degree `∑_x single x 2`, i.e. it has degree exactly `2` in each site's
own pair of variables (Tasaki eqs. (7.1.22)–(7.1.25)).  The aggregate statement
`weylMap_isHomogeneous` (total degree `2L`) follows from this one by summing the per-site degrees,
but not conversely; it is kept as the form consumed by `ProductBondDivisibility`. -/
theorem weylMap_isWeightedHomogeneous (Φ : (Fin L → Fin 3) → ℂ) :
    (weylMap Φ).IsWeightedHomogeneous (siteWeight (L := L)) (∑ x : Fin L, Finsupp.single x 2) := by
  simp only [weylMap, Fintype.linearCombination_apply]
  refine IsWeightedHomogeneous.sum _ _ _ (fun σ _ => ?_)
  rw [weylMono, smul_monomial]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_siteWeight_md σ)

end LatticeSystem.Math

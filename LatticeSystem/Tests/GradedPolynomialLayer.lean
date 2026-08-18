import LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer
import LatticeSystem.Math.MvPolynomial.WeylSpinOneMap
import LatticeSystem.Math.MvPolynomial.BilinearFactorCoprime

/-!
# Signature regression tests for the graded-polynomial layer

Usage specifications for the five declarations of
`LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer`; each `example` breaks if a signature
(argument order, implicit/explicit status, instance requirements) drifts.

* `weightedHomogeneousComponent_mul_of_isWeightedHomogeneous` — component-of-product.
* `isWeightedHomogeneous_cofactor_weight` — the cofactor (quotient) lemma, `hq0 : q ≠ 0` required
  (see the standalone negative control `LatticeSystem.Tests.GradedPolynomialLayerNegativeControl`).
* `siteWeight` — the per-site weight `Fin L × Fin 2 → (Fin L →₀ ℕ)` on the Weyl variables.
* `weylMap_isWeightedHomogeneous` — `weylMap Φ` is `siteWeight`-homogeneous of degree `2` at every
  site (the per-site refinement of the total-degree `weylMap_isHomogeneous`).
* `bondFactor_isWeightedHomogeneous` — `bondFactor a b c d` is `w`-homogeneous whenever the two
  monomials `X a * X b` and `X c * X d` carry equal weight.

No production code is written here; every proof term below is the library declaration itself.
-/

open MvPolynomial LatticeSystem.Math

namespace LatticeSystem.Tests.GradedPolynomialLayer

/-- Component-of-product: pushing a `w`-homogeneous factor `q` of degree `k` through
`weightedHomogeneousComponent w (k + m)` of a product `q * r` is the same as multiplying `q` by
the degree-`m` component of `r`. -/
example {σ M : Type*} [AddCommMonoid M] [IsLeftCancelAdd M] {w : σ → M} {q : MvPolynomial σ ℂ}
    {k : M} (hq : q.IsWeightedHomogeneous w k) (r : MvPolynomial σ ℂ) (m : M) :
    weightedHomogeneousComponent w (k + m) (q * r) = q * weightedHomogeneousComponent w m r :=
  weightedHomogeneousComponent_mul_of_isWeightedHomogeneous hq r m

/-- Cofactor (quotient) lemma: if `q` is `w`-homogeneous of degree `k`, `q ≠ 0`, and the product
`q * r` is `w`-homogeneous of degree `n`, then every monomial `d` in the support of `r` has
`k + weight w d = n`. `hq0 : q ≠ 0` is a load-bearing hypothesis, not decorative (see the negative
control). -/
example {σ M : Type*} [AddCommMonoid M] [IsLeftCancelAdd M] {w : σ → M}
    {q r : MvPolynomial σ ℂ} {k n : M}
    (hq : q.IsWeightedHomogeneous w k) (hq0 : q ≠ 0)
    (hqr : (q * r).IsWeightedHomogeneous w n)
    {d : σ →₀ ℕ} (hd : d ∈ r.support) :
    k + Finsupp.weight w d = n :=
  isWeightedHomogeneous_cofactor_weight hq hq0 hqr hd

/-- `siteWeight` assigns each Weyl variable `(x, j) : Fin L × Fin 2` to its own site `x`, valued
in the per-site degree monoid `Fin L →₀ ℕ`. -/
noncomputable example (L : ℕ) : (Fin L × Fin 2) → (Fin L →₀ ℕ) :=
  siteWeight (L := L)

/-- The Weyl image `weylMap Φ` is `siteWeight`-homogeneous with every site carrying degree `2`
(the per-site refinement of the aggregate-degree `weylMap_isHomogeneous`). -/
example (L : ℕ) (Φ : (Fin L → Fin 3) → ℂ) :
    (weylMap Φ).IsWeightedHomogeneous (siteWeight (L := L)) (∑ x : Fin L, Finsupp.single x 2) :=
  weylMap_isWeightedHomogeneous Φ

/-- `bondFactor a b c d = X a * X b - X c * X d` is `w`-homogeneous whenever its two monomials
carry equal weight. -/
example {σ M : Type*} [AddCommMonoid M] (w : σ → M) (a b c d : σ) (h : w a + w b = w c + w d) :
    (bondFactor a b c d).IsWeightedHomogeneous w (w a + w b) :=
  bondFactor_isWeightedHomogeneous w a b c d h

end LatticeSystem.Tests.GradedPolynomialLayer

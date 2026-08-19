import LatticeSystem.Math.MvPolynomial.BondFactorDerivation
import LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer
import LatticeSystem.Math.MvPolynomial.BilinearFactorCoprime

/-!
# Specification tests for the bond-factor derivation layer (PR-3a, #5292)

Signature/behaviour specification for
`LatticeSystem.Math.MvPolynomial.BondFactorDerivation` (PR-3 design round §2.1 fact (K1) and the
bidegree-lowering half of §2 "genuinely laborious" remark on `IsWeightedHomogeneous.pderiv`).

`Ω := ∂_a∂_b − ∂_c∂_d` (`bondOmega a b c d`) is the two-site derivative operator whose instance at
the bond factor `f = X a * X b - X c * X d` (`bondFactor a b c d`) drives the Casimir-descent route
to the local kernel statement `localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd`.  This file is
deliberately Math-layer only (no `AKLTUniqueness`/`weylMap` dependency);
`bondFactor (x,0) (y,1) (x,1) (y,0)` plays the role of the `L = 2` bond factor `f2` for an arbitrary
pair of distinct sites `x y : Fin L`.

Every `example` below is a signature/behaviour pin against the production declarations in
`BondFactorDerivation.lean` (there is no test runner separate from `lake build`).  The two numeric
`example`s at the bottom pin the `N = 2` sanity checks from the design round (§2.1:
`Ω(u₀²u₁²) = 0`, `Ω(f₂²) = 6·f₂`).

Required production API (all in `LatticeSystem.Math`, generic `σ` unless noted):

* `bondOmega {σ} (a b c d : σ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ` — the operator itself.
* `bondOmega_apply` — the definitional unfolding `bondOmega a b c d p = pderiv a (pderiv b p) -
  pderiv c (pderiv d p)`.
* `bondOmega_bondFactor_mul` — (K1), the pure-Leibniz commutator identity, no grading, valid for
  every `p`, stated for four pairwise-distinct variables.
* `bondOmega_bondFactor_self` — the `p = 1` instance, `Ω(bondFactor a b c d) = 2`.
* `bondOmega_isWeightedHomogeneous` — `Ω` lowers `w`-weighted bidegree by `w a + w b` (`= w c + w
  d`, forced by the two branches sharing the same target degree `n'`), for any left-cancellative
  weight monoid `M` (`IsWeightedHomogeneous.pderiv`, applied twice).
* `bondOmega_bond_mul_of_isWeightedHomogeneous` — the combined "`f2` instance" headline deliverable
  of PR-3a: for `p` `siteWeight`-homogeneous of an arbitrary per-site multidegree `D`,
  `Ω(f·p) = f·Ω p + (D x + D y + 2)•p` at the two bond sites `x y` (the bidegree form
  `D = single x m + single y n` is the two-line specialisation pinned below).

No production code is written here; every proof term is either the library declaration itself or a
short derivation from the declarations above using only pre-existing `mathlib` simp lemmas.
-/

open MvPolynomial LatticeSystem.Math

namespace LatticeSystem.Tests.BondFactorDerivation

/-! ## Signature pins -/

/-- `bondOmega` has the expected type: a two-site second-order derivative operator on
`MvPolynomial σ ℂ`. -/
noncomputable example {σ : Type*} (a b c d : σ) : MvPolynomial σ ℂ → MvPolynomial σ ℂ :=
  bondOmega a b c d

/-- Definitional content: `bondOmega a b c d p = ∂_a∂_b p − ∂_c∂_d p`. -/
example {σ : Type*} (a b c d : σ) (p : MvPolynomial σ ℂ) :
    bondOmega a b c d p = pderiv a (pderiv b p) - pderiv c (pderiv d p) :=
  bondOmega_apply a b c d p

/-! ## (K1) the pure Leibniz commutator, no grading -/

/-- **Fact (K1).**  For four pairwise-distinct variables and *any* polynomial `p` (no homogeneity
hypothesis), `Ω` applied to `bondFactor a b c d * p` splits as the bond factor times `Ω p`, plus
`2•p`, plus the four-term "boundary" sum `Σ_{i ∈ {a,b,c,d}} X i * pderiv i p`.  Purely Leibniz; the
proof never uses grading. -/
example {σ : Type*} {a b c d : σ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (p : MvPolynomial σ ℂ) :
    bondOmega a b c d (bondFactor a b c d * p)
      = bondFactor a b c d * bondOmega a b c d p + (2 : ℂ) • p
        + (X a * pderiv a p + X b * pderiv b p + X c * pderiv c p + X d * pderiv d p) :=
  bondOmega_bondFactor_mul hab hac had hbc hbd hcd p

/-- Sanity check of (K1) at `p = 1` (all four boundary terms vanish since `pderiv i 1 = 0`):
`Ω(bondFactor a b c d) = 2`. -/
example {σ : Type*} {a b c d : σ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    bondOmega a b c d (bondFactor a b c d) = (2 : MvPolynomial σ ℂ) :=
  bondOmega_bondFactor_self hab hac had hbc hbd hcd

/-! ## `Ω` lowers the weighted bidegree -/

/-- **Bidegree lowering.**  If `p` is `w`-homogeneous of weighted degree `n`, and `n'` is the
common complementary degree for both derivative branches (`n' + (w a + w b) = n = n' + (w c + w
d)`), then `bondOmega a b c d p` is `w`-homogeneous of degree `n'`.  A two-fold application of
`IsWeightedHomogeneous.pderiv` (`Mathlib.RingTheory.MvPolynomial.EulerIdentity`); no `Fintype σ`
needed. -/
example {σ M : Type*} [AddCancelCommMonoid M] {w : σ → M} {a b c d : σ} {n n' : M}
    (hab : n' + (w a + w b) = n) (hcd : n' + (w c + w d) = n)
    {p : MvPolynomial σ ℂ} (hp : p.IsWeightedHomogeneous w n) :
    (bondOmega a b c d p).IsWeightedHomogeneous w n' :=
  bondOmega_isWeightedHomogeneous hab hcd hp

/-! ## The combined "bond instance" (headline PR-3a deliverable)

`bondFactor (x,0) (y,1) (x,1) (y,0)` on `MvPolynomial (Fin L × Fin 2) ℂ` is the two-site bond
factor for the pair of distinct sites `x y : Fin L` (`= f2` at `L = 2`, `x = 0`, `y = 1`). -/

/-- **Headline deliverable.**  Combining (K1) with the per-site Euler identity (through
`siteWeight`-homogeneity of `p` at an arbitrary per-site multidegree `D`): `Ω(f·p) = f·Ω p +
(D x + D y + 2)•p`; the degrees away from the bond `{x, y}` are unconstrained. -/
example {L : ℕ} {x y : Fin L} (hxy : x ≠ y) {D : Fin L →₀ ℕ}
    {p : MvPolynomial (Fin L × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := L)) D) :
    bondOmega (x, 0) (y, 1) (x, 1) (y, 0) (bondFactor (x, 0) (y, 1) (x, 1) (y, 0) * p)
      = bondFactor (x, 0) (y, 1) (x, 1) (y, 0) * bondOmega (x, 0) (y, 1) (x, 1) (y, 0) p
        + ((D x + D y + 2 : ℕ) : ℂ) • p :=
  bondOmega_bond_mul_of_isWeightedHomogeneous hxy hp

/-- The per-site bidegree `(m, n)` form is the two-line specialisation `D = single x m + single y n`
of the headline instance, `Ω(f·p) = f·Ω p + (m+n+2)•p`; it needs no separate library declaration. -/
example {L : ℕ} {x y : Fin L} (hxy : x ≠ y) {m n : ℕ} {p : MvPolynomial (Fin L × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := L))
      (Finsupp.single x m + Finsupp.single y n)) :
    bondOmega (x, 0) (y, 1) (x, 1) (y, 0) (bondFactor (x, 0) (y, 1) (x, 1) (y, 0) * p)
      = bondFactor (x, 0) (y, 1) (x, 1) (y, 0) * bondOmega (x, 0) (y, 1) (x, 1) (y, 0) p
        + ((m + n + 2 : ℕ) : ℂ) • p := by
  simpa [hxy, hxy.symm] using bondOmega_bond_mul_of_isWeightedHomogeneous hxy hp

/-! ## `N = 2` numeric checks (design round §2.1: `Ω(u₀²u₁²) = 0`, `Ω(f₂²) = 6f₂`) -/

/-- `Ω(u₀²u₁²) = 0` at `N = 2`: `u₀²u₁²` has site-`0` degree `2` from `u₀` alone and site-`1`
degree `2` from `u₁` alone, so neither derivative branch of `Ω` sees both of its variables. -/
example :
    bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0)
        ((X (0, 0) : MvPolynomial (Fin 2 × Fin 2) ℂ) ^ 2 * X (1, 0) ^ 2)
      = 0 := by
  rw [bondOmega_apply]
  have h2 : (pderiv ((0 : Fin 2), (1 : Fin 2))) (2 : MvPolynomial (Fin 2 × Fin 2) ℂ) = 0 := by
    simpa using (pderiv (R := ℂ) ((0 : Fin 2), (1 : Fin 2))).map_natCast 2
  simp [h2, Prod.mk.injEq]

/-- `Ω(f₂²) = 6·f₂` at `N = 2` (design round §2.1, the `Ĉ p = 0` check on `p = f₂²`, `J = 0`):
derived from the headline instance applied at `p = f₂` itself (`m = n = 1`) together with `Ω f₂ =
2`. -/
example :
    bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0)
        (bondFactor ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0)
          * bondFactor ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0))
      = (6 : ℂ) • bondFactor ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) := by
  have hxy : (0 : Fin 2) ≠ 1 := by decide
  have hp : (bondFactor ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0)).IsWeightedHomogeneous
      (siteWeight (L := 2)) (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) := by
    have := bondFactor_isWeightedHomogeneous (siteWeight (L := 2))
      ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) (by simp [siteWeight])
    simpa [siteWeight] using this
  have hΩf2 : bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0)
      (bondFactor ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0))
      = (2 : MvPolynomial (Fin 2 × Fin 2) ℂ) := by
    apply bondOmega_bondFactor_self <;> decide
  have hD : ((Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 0
      + (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 1 + 2 : ℕ)
      = 4 := by
    simp
  rw [bondOmega_bond_mul_of_isWeightedHomogeneous hxy hp, hΩf2, mul_two, hD]
  push_cast
  module

end LatticeSystem.Tests.BondFactorDerivation

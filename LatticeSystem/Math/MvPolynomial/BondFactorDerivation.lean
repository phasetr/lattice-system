/-
Second-order bond derivations of a multivariate polynomial ring.

For four variables `a, b, c, d` of `MvPolynomial σ ℂ` this file introduces the second-order
operator

  `Ω = bondOmega a b c d = ∂_a ∂_b - ∂_c ∂_d`,

the derivation-side partner of the bilinear bond factor
`f = bondFactor a b c d = X a * X b - X c * X d` of
`LatticeSystem.Math.MvPolynomial.BilinearFactorCoprime`.  The algebraic fact proved here is the
commutator of `Ω` with multiplication by `f`: for pairwise distinct `a, b, c, d` and *every* `p`
(no grading hypothesis whatsoever),

  `Ω (f * p) = f * Ω p + 2 • p + ∑_{i ∈ {a, b, c, d}} X i * ∂_i p`.

This is a pure Leibniz computation whose only inputs are `∂_a f = X b`, `∂_b f = X a`,
`∂_c f = -X d` and `∂_d f = -X c`.  Two consequences are recorded:

* `bondOmega_isWeightedHomogeneous` — `Ω` lowers the `w`-weighted degree by `w a + w b`
  (`= w c + w d`, both branches sharing the same target degree), a double application of
  `MvPolynomial.IsWeightedHomogeneous.pderiv`; no finiteness of `σ` is needed.
* `bondOmega_bond_mul_of_isWeightedHomogeneous` — the two-site instance.  For two distinct sites
  `x ≠ y` of the Weyl variables `Fin L × Fin 2` the bond factor is
  `f_{xy} = u_x v_y - v_x u_y = bondFactor (x,0) (y,1) (x,1) (y,0)`, and the four-term boundary sum
  above splits into the two per-site Euler operators `X (x,0) * ∂_(x,0) + X (x,1) * ∂_(x,1)`.  On a
  `siteWeight`-homogeneous `p` of arbitrary per-site multidegree `D : Fin L →₀ ℕ` those evaluate to
  `(D x) • p` and `(D y) • p` (Euler's identity
  `MvPolynomial.IsWeightedHomogeneous.sum_weight_X_mul_pderiv`, applied one site at a time through
  the `ℕ`-valued weight that selects that site's two variables), so that

  `Ω (f_{xy} * p) = f_{xy} * Ω p + (D x + D y + 2) • p`,

  with the degrees off the bond playing no role (so the uniform degree `D = ∑_z single z N` of the
  Weyl image of a spin-`S` chain state is covered on the same footing as a two-site bidegree).

The `p = 1` instance `Ω f = 2` (`bondOmega_bondFactor_self`) is the normalisation that fixes the
constant `2`.

Independently of the commutator, the two-site operator `f_{xy} Ω` itself is *distributed* into four
site-separated second-order terms (`bondFactor_mul_bondOmega_two_site`),

  `f_{xy} Ω = a_x b_y + b_x a_y − (u_x∂_{v_x})(v_y∂_{u_y}) − (v_x∂_{u_x})(u_y∂_{v_y})`,
  `a_x = u_x∂_{u_x}`, `b_x = v_x∂_{v_x}`,

again for every `p` and with `x ≠ y` the only input.  Each factor is the Weyl transport of a
single-site spin operator, so this identity is what turns the two-site Casimir into `N(N+1) − f Ω`;
the per-site Euler identity `site_euler` supplies the `a_x + b_x = (deg_x) ·` half of that reduction
and is exported for the same consumer.

This is the derivation layer of the Casimir descent for the uniqueness of the spin-`S` valence-bond
ground state: under the Weyl (Schwinger-boson) representation the two-site Casimir operator acts as
`N (N + 1) - f_{xy} Ω`, so multiplication by `f_{xy}` shifts the Casimir eigenvalue exactly by the
`(m + n + 2)` recorded above.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, 2020),
§7.1.3 "The Uniqueness of the Ground State", pp. 186–188, eqs. (7.1.22)–(7.1.25); polynomial
representation due to Arovas–Auerbach–Haldane [10]; proof due to Kennedy–Lieb–Tasaki [41].
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import LatticeSystem.Math.MvPolynomial.BilinearFactorCoprime
import LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer

open MvPolynomial

namespace LatticeSystem.Math

variable {σ : Type*}

/-- The second-order bond derivation `Ω = ∂_a ∂_b - ∂_c ∂_d` attached to the four variables of the
bilinear bond factor `bondFactor a b c d = X a * X b - X c * X d`. -/
noncomputable def bondOmega (a b c d : σ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  pderiv a (pderiv b p) - pderiv c (pderiv d p)

/-- Definitional unfolding of `bondOmega`. -/
theorem bondOmega_apply (a b c d : σ) (p : MvPolynomial σ ℂ) :
    bondOmega a b c d p = pderiv a (pderiv b p) - pderiv c (pderiv d p) :=
  rfl

/-- The four first-order derivatives of the bond factor on four distinct variables:
`∂_a f = X b`, `∂_b f = X a`, `∂_c f = -X d`, `∂_d f = -X c`.  Bundled into a single lemma because
the (K1) commutator uses all four and each is the same two-line `simp`. -/
private theorem pderiv_bondFactor {a b c d : σ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    pderiv a (bondFactor a b c d) = X b ∧ pderiv b (bondFactor a b c d) = X a ∧
      pderiv c (bondFactor a b c d) = -X d ∧ pderiv d (bondFactor a b c d) = -X c := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [bondFactor, map_sub, pderiv_X_self, pderiv_X_of_ne, hab, hab.symm, hac,
      hac.symm, had, had.symm, hbc, hbc.symm, hbd, hbd.symm, hcd, hcd.symm]

/-- **The bond commutator (fact K1).**  For four pairwise distinct variables and *any* polynomial
`p` — no homogeneity hypothesis — the bond derivation `Ω = ∂_a∂_b - ∂_c∂_d` commutes with
multiplication by `bondFactor a b c d` up to `2 • p` and the four-term boundary sum
`∑_{i ∈ {a,b,c,d}} X i * ∂_i p`.

The proof is pure Leibniz: `∂_b (f * p) = X a * p + f * ∂_b p`, then `∂_a` of that produces
`p + X a * ∂_a p` from the first summand and `X b * ∂_b p + f * ∂_a∂_b p` from the second; the
`c, d` branch is the same computation with the two sign-carrying derivatives `∂_c f = -X d`,
`∂_d f = -X c`, and contributes the second copy of `p`. -/
theorem bondOmega_bondFactor_mul {a b c d : σ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (p : MvPolynomial σ ℂ) :
    bondOmega a b c d (bondFactor a b c d * p)
      = bondFactor a b c d * bondOmega a b c d p + (2 : ℂ) • p
        + (X a * pderiv a p + X b * pderiv b p + X c * pderiv c p + X d * pderiv d p) := by
  obtain ⟨hfa, hfb, hfc, hfd⟩ := pderiv_bondFactor hab hac had hbc hbd hcd
  have hleibB : pderiv b (bondFactor a b c d * p) = X a * p + bondFactor a b c d * pderiv b p := by
    rw [pderiv_mul, hfb]
  have hleibAB : pderiv a (pderiv b (bondFactor a b c d * p))
      = p + X a * pderiv a p + (X b * pderiv b p
        + bondFactor a b c d * pderiv a (pderiv b p)) := by
    rw [hleibB, map_add, pderiv_mul, pderiv_mul, hfa, pderiv_X_self]
    ring
  have hleibD : pderiv d (bondFactor a b c d * p)
      = -(X c * p) + bondFactor a b c d * pderiv d p := by
    rw [pderiv_mul, hfd]
    ring
  have hleibCD : pderiv c (pderiv d (bondFactor a b c d * p))
      = -(p + X c * pderiv c p) + (-(X d * pderiv d p)
        + bondFactor a b c d * pderiv c (pderiv d p)) := by
    rw [hleibD, map_add, map_neg, pderiv_mul, pderiv_mul, hfc, pderiv_X_self]
    ring
  simp only [bondOmega_apply]
  rw [hleibAB, hleibCD, two_smul ℂ p]
  ring

/-- **Normalisation.**  The `p = 1` instance of the bond commutator: every boundary term vanishes
(`∂_i 1 = 0`) and `Ω 1 = 0`, leaving `Ω (bondFactor a b c d) = 2`. -/
theorem bondOmega_bondFactor_self {a b c d : σ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    bondOmega a b c d (bondFactor a b c d) = (2 : MvPolynomial σ ℂ) := by
  have h1 : bondOmega a b c d (1 : MvPolynomial σ ℂ) = 0 := by
    simp [bondOmega_apply]
  have h := bondOmega_bondFactor_mul hab hac had hbc hbd hcd 1
  rw [mul_one, h1, mul_zero] at h
  rw [h]
  simp [two_smul, one_add_one_eq_two]

/-- **Bidegree lowering.**  `Ω = ∂_a∂_b - ∂_c∂_d` lowers the `w`-weighted degree by `w a + w b`,
which is also `w c + w d` since both branches are required to land in the same degree `n'`.  Twice
`MvPolynomial.IsWeightedHomogeneous.pderiv`; left cancellation in `M` is what the two `pderiv`
steps consume, and no finiteness of `σ` enters. -/
theorem bondOmega_isWeightedHomogeneous {M : Type*} [AddCancelCommMonoid M] {w : σ → M}
    {a b c d : σ} {n n' : M} (hab : n' + (w a + w b) = n) (hcd : n' + (w c + w d) = n)
    {p : MvPolynomial σ ℂ} (hp : p.IsWeightedHomogeneous w n) :
    (bondOmega a b c d p).IsWeightedHomogeneous w n' := by
  have h1 : (pderiv b p).IsWeightedHomogeneous w (n' + w a) :=
    hp.pderiv (by rw [add_assoc]; exact hab)
  have h2 : (pderiv d p).IsWeightedHomogeneous w (n' + w c) :=
    hp.pderiv (by rw [add_assoc]; exact hcd)
  exact (weightedHomogeneousSubmodule ℂ w n').sub_mem (h1.pderiv rfl) (h2.pderiv rfl)

variable {L : ℕ}

/-- The `ℕ`-valued weight that selects the two Weyl variables `u_x = (x,0)`, `v_x = (x,1)` of a
single site `x`, both with weight `1`.  It is the site-`x` component of the `Finsupp`-valued
`siteWeight`, and exists only because Euler's identity
`MvPolynomial.IsWeightedHomogeneous.sum_weight_X_mul_pderiv` is stated for `ℕ`-valued weights. -/
private def siteDegWeight (x : Fin L) : Fin L × Fin 2 → ℕ := fun e => if e.1 = x then 1 else 0

/-- The `siteDegWeight x`-weight of a multidegree is the exponent sum `d (x,0) + d (x,1)` of the
two Weyl variables of site `x`, i.e. the site-`x` component of `weight_siteWeight_apply`. -/
private theorem weight_siteDegWeight_apply (x : Fin L) (d : (Fin L × Fin 2) →₀ ℕ) :
    Finsupp.weight (siteDegWeight x) d = d (x, 0) + d (x, 1) := by
  classical
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype d (fun i c => c • siteDegWeight x i)
      (fun i => zero_smul ℕ (siteDegWeight x i)),
    Fintype.sum_prod_type, Finset.sum_eq_single x]
  · simp [siteDegWeight, Fin.sum_univ_two]
  · intro y _ hyx
    simp [siteDegWeight, hyx]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- A `siteWeight`-homogeneous polynomial of degree `D` is `siteDegWeight x`-homogeneous of degree
`D x`: the per-site grading is the component-wise refinement of the single-site one. -/
private theorem isWeightedHomogeneous_siteDegWeight {x : Fin L} {D : Fin L →₀ ℕ}
    {p : MvPolynomial (Fin L × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := L)) D) :
    p.IsWeightedHomogeneous (siteDegWeight x) (D x) := by
  intro d hd
  rw [weight_siteDegWeight_apply, ← weight_siteWeight_apply d x, hp hd]

/-- **Per-site Euler identity.**  On a `siteWeight`-homogeneous polynomial of per-site degree `D`
the Euler operator of a single site `x` — the two-term sum over that site's own Weyl variables —
multiplies by the degree `D x` of that site.

It is the diagonal half of the Weyl dictionary: together with
`bondFactor_mul_bondOmega_two_site` it is what collapses the `(a_x + b_x)(a_y + b_y)` part of the
two-site Casimir to the scalar `N²` on a Weyl image. -/
theorem site_euler {x : Fin L} {D : Fin L →₀ ℕ} {p : MvPolynomial (Fin L × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := L)) D) :
    X (x, 0) * pderiv (x, 0) p + X (x, 1) * pderiv (x, 1) p = (D x) • p := by
  have hsum : ∑ i : Fin L × Fin 2, siteDegWeight x i • (X i * pderiv i p)
      = X (x, 0) * pderiv (x, 0) p + X (x, 1) * pderiv (x, 1) p := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
    · simp [siteDegWeight, Fin.sum_univ_two]
    · intro y _ hyx
      simp [siteDegWeight, hyx]
    · intro h
      exact absurd (Finset.mem_univ x) h
  rw [← hsum, (isWeightedHomogeneous_siteDegWeight (x := x) hp).sum_weight_X_mul_pderiv]

/-- **The two-site bond instance (the headline of the derivation layer).**  For two distinct sites
`x ≠ y` of the Weyl variables `Fin L × Fin 2`, with bond factor
`f_{xy} = bondFactor (x,0) (y,1) (x,1) (y,0) = u_x v_y - v_x u_y`, and a `siteWeight`-homogeneous
`p` of arbitrary per-site multidegree `D : Fin L →₀ ℕ`, the boundary sum of the bond commutator
collapses site by site through Euler's identity, leaving only the two bond sites:

  `Ω (f_{xy} * p) = f_{xy} * Ω p + (D x + D y + 2) • p`.

The degrees at the sites other than `x, y` are irrelevant, so no constraint on `D` off the bond is
imposed; the per-site bidegree `(m, n)` instance is `D = single x m + single y n`.

Under the Weyl representation of the spin-`S` chain this is the statement that multiplying by the
bond factor shifts the two-site Casimir eigenvalue by exactly `D x + D y + 2`. -/
theorem bondOmega_bond_mul_of_isWeightedHomogeneous {x y : Fin L} (hxy : x ≠ y) {D : Fin L →₀ ℕ}
    {p : MvPolynomial (Fin L × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := L)) D) :
    bondOmega (x, 0) (y, 1) (x, 1) (y, 0) (bondFactor (x, 0) (y, 1) (x, 1) (y, 0) * p)
      = bondFactor (x, 0) (y, 1) (x, 1) (y, 0) * bondOmega (x, 0) (y, 1) (x, 1) (y, 0) p
        + ((D x + D y + 2 : ℕ) : ℂ) • p := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hab : ((x, 0) : Fin L × Fin 2) ≠ (y, 1) := fun h => hxy (congrArg Prod.fst h)
  have hac : ((x, 0) : Fin L × Fin 2) ≠ (x, 1) := fun h => h01 (congrArg Prod.snd h)
  have had : ((x, 0) : Fin L × Fin 2) ≠ (y, 0) := fun h => hxy (congrArg Prod.fst h)
  have hbc : ((y, 1) : Fin L × Fin 2) ≠ (x, 1) := fun h => hxy.symm (congrArg Prod.fst h)
  have hbd : ((y, 1) : Fin L × Fin 2) ≠ (y, 0) := fun h => h01.symm (congrArg Prod.snd h)
  have hcd : ((x, 1) : Fin L × Fin 2) ≠ (y, 0) := fun h => hxy (congrArg Prod.fst h)
  have hEx := site_euler (x := x) hp
  have hEy := site_euler (x := y) hp
  rw [bondOmega_bondFactor_mul hab hac had hbc hbd hcd p]
  have hbdry : X ((x, 0) : Fin L × Fin 2) * pderiv (x, 0) p + X (y, 1) * pderiv (y, 1) p
      + X (x, 1) * pderiv (x, 1) p + X (y, 0) * pderiv (y, 0) p = (D x) • p + (D y) • p := by
    rw [← hEx, ← hEy]
    ring
  rw [hbdry, ← Nat.cast_smul_eq_nsmul ℂ (D x) p, ← Nat.cast_smul_eq_nsmul ℂ (D y) p]
  push_cast
  module

/-- **The universal two-site distribution.**  Multiplication by the bond factor
`f_{xy} = u_x v_y − v_x u_y` composed with the bond derivation `Ω = ∂_{u_x}∂_{v_y} − ∂_{v_x}∂_{u_y}`
is, on *every* polynomial and with no grading hypothesis, the four-term operator

  `f_{xy} Ω = a_x b_y + b_x a_y − (u_x∂_{v_x})(v_y∂_{u_y}) − (v_x∂_{u_x})(u_y∂_{v_y})`

in which each of the eight factors involves the two variables of a *single* site.  The only input is
`x ≠ y`: it makes the inner `∂(X)` contribution of each Leibniz expansion vanish, because the
differentiated variable belongs to the other site.

The four composite terms are exactly the Weyl transports of `Ŝ^{(3)}`- and `Ŝ^±`-type two-site
products, which is how the identity converts the spin dot product into `f_{xy} Ω` plus the Euler
part `¼(a_x + b_x)(a_y + b_y)`. -/
theorem bondFactor_mul_bondOmega_two_site {x y : Fin L} (hxy : x ≠ y)
    (p : MvPolynomial (Fin L × Fin 2) ℂ) :
    bondFactor ((x, 0) : Fin L × Fin 2) (y, 1) (x, 1) (y, 0)
        * bondOmega ((x, 0) : Fin L × Fin 2) (y, 1) (x, 1) (y, 0) p
      = X (x, 0) * pderiv (x, 0) (X (y, 1) * pderiv (y, 1) p)
        + X (x, 1) * pderiv (x, 1) (X (y, 0) * pderiv (y, 0) p)
        - X (x, 0) * pderiv (x, 1) (X (y, 1) * pderiv (y, 0) p)
        - X (x, 1) * pderiv (x, 0) (X (y, 0) * pderiv (y, 1) p) := by
  have hzero : ∀ i j : Fin 2, pderiv ((x, j) : Fin L × Fin 2)
      (X ((y, i) : Fin L × Fin 2) : MvPolynomial (Fin L × Fin 2) ℂ) = 0 :=
    fun _ _ => pderiv_X_of_ne fun h => hxy.symm (congrArg Prod.fst h)
  rw [bondFactor, bondOmega_apply]
  simp only [pderiv_mul, hzero, zero_mul, zero_add]
  ring

end LatticeSystem.Math

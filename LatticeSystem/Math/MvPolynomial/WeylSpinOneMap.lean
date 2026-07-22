/-
The Weyl (Schwinger-boson) linear map for a chain of spin-`1` sites.

This file constructs the injective linear map that sends a many-body spin-`1` state
`Φ : (Fin L → Fin 3) → ℂ` to a homogeneous polynomial of total degree `2L` in the `2L` Weyl
variables `Fin L × Fin 2` (site `x` carrying `u_x = (x,0)` and `v_x = (x,1)`).  Each site basis
state `m ∈ {0,1,2}` (physically `S^z = +1, 0, -1`) maps to a degree-`2` monomial in that site's
two variables:

  `m = 0 ↦ u_x^2`,  `m = 1 ↦ u_x v_x`,  `m = 2 ↦ v_x^2`.

This is the "Stage C" Weyl representation used in the uniqueness proof of the AKLT ground state
(Tasaki §7.1.3, eqs. (7.1.22)–(7.1.23)); the bond-divisibility / UFD argument that consumes this
map lives in `LatticeSystem.Math.MvPolynomial.BilinearFactorCoprime`.  We only need the map to be
`ℂ`-linear, injective, and image-homogeneous of degree `2L`; the physical normalisation constants
(e.g. `√2` on `u_x v_x`) are irrelevant to a linear injection and are dropped.

The single-monomial image `weylMono σ` (rather than the product form `∏ X`) is used deliberately;
the bridge to the product form `∏_x (u_x v_{x+1} - v_x u_{x+1})` belongs to a later stage.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, 2020),
§7.1.3 "The Uniqueness of the Ground State", pp. 186–188, eqs. (7.1.22)–(7.1.25); polynomial
representation due to Arovas–Auerbach–Haldane [10]; proof due to Kennedy–Lieb–Tasaki [41].
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open MvPolynomial

namespace LatticeSystem.Math

variable {L : ℕ}

/-- The degree-`2` multidegree contributed by a single spin-`1` site `x` in state `k : Fin 3`, as
an exponent `Finsupp` on the Weyl variables `Fin L × Fin 2` (`(x,0) = u_x`, `(x,1) = v_x`):
`k = 0 ↦ u_x^2`, `k = 1 ↦ u_x v_x`, `k = 2 ↦ v_x^2`. -/
noncomputable def mdSite (x : Fin L) (k : Fin 3) : (Fin L × Fin 2) →₀ ℕ :=
  ![Finsupp.single (x, 0) 2,
    Finsupp.single (x, 0) 1 + Finsupp.single (x, 1) 1,
    Finsupp.single (x, 1) 2] k

/-- Each single-site multidegree has total degree `2` (each site contributes a degree-`2`
monomial), so a chain of `L` sites yields total degree `2L`. -/
theorem mdSite_degree (x : Fin L) (k : Fin 3) : (mdSite x k).degree = 2 := by
  fin_cases k <;>
    simp [mdSite, map_add]

/-- Value of a single-site multidegree at the first (`u`) variable of its own site: reading this
coordinate recovers `k` via `k ↦ 2 - k`, which underlies injectivity of `md`. -/
theorem mdSite_apply_self (x : Fin L) (k : Fin 3) : (mdSite x k) (x, 0) = 2 - (k : ℕ) := by
  fin_cases k <;>
    simp [mdSite, Finsupp.add_apply, Prod.ext_iff]

/-- A single-site multidegree vanishes at any variable belonging to a different site `y ≠ x`. -/
theorem mdSite_apply_ne {x y : Fin L} (h : y ≠ x) (k : Fin 3) : (mdSite y k) (x, 0) = 0 := by
  fin_cases k <;>
    simp [mdSite, Finsupp.add_apply, Prod.ext_iff, h]

/-- The total multidegree of a chain state `σ`, i.e. the sum of the per-site degree-`2`
multidegrees; its coefficient `1` monomial is the Weyl image `weylMono σ`. -/
noncomputable def md (σ : Fin L → Fin 3) : (Fin L × Fin 2) →₀ ℕ :=
  ∑ x, mdSite x (σ x)

/-- Reading the first (`u`) variable of site `i` recovers the site state via `σ i ↦ 2 - σ i`;
this is the key computation for injectivity of `md`. -/
theorem md_apply_fst (σ : Fin L → Fin 3) (i : Fin L) : (md σ) (i, 0) = 2 - (σ i : ℕ) := by
  rw [md, Finsupp.finset_sum_apply,
    Finset.sum_eq_single i (fun y _ hy => mdSite_apply_ne hy (σ y))
      (fun h => absurd (Finset.mem_univ i) h)]
  exact mdSite_apply_self i (σ i)

/-- The total multidegree of every chain state is `2L` (each of the `L` sites contributes `2`);
hence every Weyl monomial is homogeneous of total degree `2L` (Tasaki eq. (7.1.25)). -/
theorem md_degree (σ : Fin L → Fin 3) : (md σ).degree = 2 * L := by
  rw [md, map_sum]
  simp only [mdSite_degree]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]

/-- Distinct chain states have distinct multidegrees: reading each site's first variable via
`md_apply_fst` recovers `σ i` from `md σ`, so `md` is injective (the Weyl representation is
faithful on the standard basis). -/
theorem md_injective : Function.Injective (md : (Fin L → Fin 3) → _) := by
  intro σ τ h
  funext i
  have hi : (md σ) (i, 0) = (md τ) (i, 0) := by rw [h]
  rw [md_apply_fst, md_apply_fst] at hi
  have hσ : (σ i : ℕ) < 3 := (σ i).isLt
  have hτ : (τ i : ℕ) < 3 := (τ i).isLt
  exact Fin.ext (by omega)

/-- The Weyl image of the standard basis vector `σ`: the single degree-`2L` monomial `X^{md σ}`
(Tasaki eqs. (7.1.22)–(7.1.23)).  A single monomial is used (not the product form `∏ X`). -/
noncomputable def weylMono (σ : Fin L → Fin 3) : MvPolynomial (Fin L × Fin 2) ℂ :=
  MvPolynomial.monomial (md σ) 1

/-- The Weyl (Schwinger-boson) linear map `Φ ↦ ∑_σ Φ σ • X^{md σ}` from many-body spin-`1` states
to polynomials in the `2L` Weyl variables (Tasaki §7.1.3, eq. (7.1.22)).  It is injective with
image homogeneous of total degree `2L`. -/
noncomputable def weylMap : ((Fin L → Fin 3) → ℂ) →ₗ[ℂ] MvPolynomial (Fin L × Fin 2) ℂ :=
  Fintype.linearCombination ℂ weylMono

/-- The coefficient of the monomial `X^{md τ}` in `weylMap Φ` is exactly `Φ τ` (the Weyl monomials
are a linearly independent family indexed by the standard basis).  Publicly exposed: consumed by
the bond-divisibility / dimension-count stages. -/
theorem weylMap_coeff (Φ : (Fin L → Fin 3) → ℂ) (τ : Fin L → Fin 3) :
    (weylMap Φ).coeff (md τ) = Φ τ := by
  classical
  simp only [weylMap, Fintype.linearCombination_apply, weylMono, coeff_sum, smul_monomial,
    smul_eq_mul, mul_one, coeff_monomial, md_injective.eq_iff]
  exact Fintype.sum_ite_eq' τ Φ

/-- The Weyl map is injective: distinct states have distinct images, since the coefficient at
`X^{md σ}` reads off `Φ σ` (`weylMap_coeff`). -/
theorem weylMap_injective : Function.Injective (weylMap : ((Fin L → Fin 3) → ℂ) →ₗ[ℂ] _) := by
  intro Φ Ψ h
  funext σ
  have := congrArg (fun p => MvPolynomial.coeff (md σ) p) h
  simpa only [weylMap_coeff] using this

/-- The image `weylMap Φ` is homogeneous of total degree `2L` (each Weyl monomial `X^{md σ}` has
degree `md σ`.degree `= 2L`; Tasaki eq. (7.1.25)). -/
theorem weylMap_isHomogeneous (Φ : (Fin L → Fin 3) → ℂ) :
    (weylMap Φ).IsHomogeneous (2 * L) := by
  simp only [weylMap, Fintype.linearCombination_apply]
  refine IsHomogeneous.sum _ _ _ (fun σ _ => ?_)
  rw [weylMono, smul_monomial]
  exact isHomogeneous_monomial _ (md_degree σ)

end LatticeSystem.Math

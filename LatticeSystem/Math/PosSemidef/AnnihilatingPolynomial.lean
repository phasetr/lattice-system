import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Matrix.Order

/-!
# Positive semidefiniteness from an annihilating polynomial with distinct real nodes

If a Hermitian matrix `A` is annihilated by the nodal polynomial of pairwise distinct real nodes
`r i`, that is `aeval A (∏_i (X − r i)) = 0`, and a real polynomial `q` of degree `< card ι` is
nonnegative at every node, then `aeval A q` is positive semidefinite.  The route is Lagrange
interpolation: `q = Σ_i q(r i) • basis i`, each Lagrange basis polynomial `basis i` becomes a
Hermitian idempotent under `aeval A` (so `aeval A (basis i) = Pᴴ P` for `P = aeval A (basis i)`
itself), and a nonnegative combination of positive-semidefinite matrices is positive semidefinite.

This is the generic layer behind the AKLT bond-term positivity of Tasaki §7.3.1 (eq. (7.3.3),
p. 208): the bond Casimir `Ĉ` satisfies the annihilating polynomial
`∏_{J=0}^{N} (Ĉ − J(J+1)) = 0` (`GeneralSCasimirSpectrum.aeval_nodal_bondCasimirS`), and the
penalty polynomial `q_S` is nonnegative at every node `J(J+1)`
(`GeneralSOpenChainBondTerm.casimirPenaltyWeight_eq_zero` / `_pos`).  No projection operator is
exported by this module: the Lagrange basis stays private, so there is no collision with the
named spin-level projector `bondMaxSpinProjectionS` (`GeneralAKLT.lean`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.3.1, eqs. (7.3.1)–(7.3.3), pp. 208–209.
-/

open Matrix

namespace LatticeSystem.Math

open scoped ComplexOrder

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- **`aeval A` of a real polynomial is Hermitian when `A` is.**  Real coefficients are true *by
type* (`p : Polynomial ℝ`), so no `star`-of-polynomial hypothesis is needed. -/
private theorem isHermitian_aeval_real {A : Matrix n n ℂ} (hA : A.IsHermitian) (p : Polynomial ℝ) :
    (Polynomial.aeval A p).IsHermitian := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Finset.sum_induction _ _ (fun _ _ => Matrix.IsHermitian.add) Matrix.isHermitian_zero
    fun i _ => ?_
  exact (hA.pow i).smul (IsSelfAdjoint.all (p.coeff i))

/-- **A polynomial vanishing at every node of an injective family is divisible by the nodal
polynomial.**  `Lagrange.nodal Finset.univ r = ∏_i (X − C (r i))`; pairwise coprimality of the
factors (`Polynomial.pairwise_coprime_X_sub_C`) upgrades "vanishes at each root" to
"divisible by the product" (`Polynomial.dvd_iff_isRoot`, `Finset.prod_dvd_of_coprime`). -/
private theorem nodal_dvd_of_eval_eq_zero {r : ι → ℝ} (hr : Function.Injective r)
    {p : Polynomial ℝ} (hp : ∀ i, p.eval (r i) = 0) : Lagrange.nodal Finset.univ r ∣ p := by
  rw [Lagrange.nodal_eq]
  exact Finset.prod_dvd_of_coprime (fun i _ j _ hij => Polynomial.pairwise_coprime_X_sub_C hr hij)
    fun i _ => Polynomial.dvd_iff_isRoot.mpr (hp i)

/-- **The Lagrange basis polynomials become Hermitian idempotents under `aeval A`.**  If `A` is
Hermitian and annihilates the nodal polynomial of an injective node family, then for every index
`i` the matrix `aeval A (Lagrange.basis Finset.univ r i)` is positive semidefinite: `(basis i)² −
basis i` vanishes at every node, hence is divisible by the nodal polynomial, hence `aeval A` of it
is `0`, i.e. the image is Hermitian idempotent `P`, so `P = Pᴴ P` and
`Matrix.posSemidef_conjTranspose_mul_self` applies. -/
private theorem posSemidef_aeval_lagrangeBasis [DecidableEq ι] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {r : ι → ℝ} (hr : Function.Injective r)
    (hnodal : Polynomial.aeval A (Lagrange.nodal Finset.univ r) = 0) (i : ι) :
    (Polynomial.aeval A (Lagrange.basis Finset.univ r i)).PosSemidef := by
  have hdvd : Lagrange.nodal Finset.univ r ∣
      Lagrange.basis (Finset.univ : Finset ι) r i ^ 2 - Lagrange.basis Finset.univ r i := by
    refine nodal_dvd_of_eval_eq_zero hr fun j => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_pow]
    rcases eq_or_ne i j with rfl | hij
    · rw [Lagrange.eval_basis_self hr.injOn (Finset.mem_univ i)]
      ring
    · rw [Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]
      ring
  obtain ⟨w, hw⟩ := hdvd
  have hidem : Polynomial.aeval A (Lagrange.basis (Finset.univ : Finset ι) r i)
      * Polynomial.aeval A (Lagrange.basis Finset.univ r i)
      = Polynomial.aeval A (Lagrange.basis Finset.univ r i) := by
    have h := congrArg (Polynomial.aeval A) hw
    rw [map_sub, map_pow, map_mul, hnodal, zero_mul, sub_eq_zero, sq] at h
    exact h
  have hherm : (Polynomial.aeval A (Lagrange.basis (Finset.univ : Finset ι) r i)).IsHermitian :=
    isHermitian_aeval_real hA _
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self
    (Polynomial.aeval A (Lagrange.basis (Finset.univ : Finset ι) r i))
  rwa [hherm.eq, hidem] at hPSD

/-- **Positivity from an annihilating polynomial with distinct real nodes.**  If `A` is Hermitian
and annihilates the nodal polynomial of an injective real family `r : ι → ℝ`
(`card ι` nodes), then every real polynomial `q` of degree `< card ι` that is nonnegative at every
node `r i` has `aeval A q` positive semidefinite.

Route: `q = Lagrange.interpolate Finset.univ r (q.eval ∘ r)` by degree + injectivity
(`Lagrange.eq_interpolate_of_eval_eq`), which unfolds to `Σ_i q(r i) • basis i`
(`Lagrange.interpolate_apply`); each term is a nonnegative real scalar times a positive-semidefinite
matrix (`posSemidef_aeval_lagrangeBasis`), and a nonnegative sum of positive-semidefinite matrices
is positive semidefinite (`Matrix.PosSemidef.add`/`.zero`/`.smul`). -/
theorem posSemidef_aeval_of_aeval_nodal_eq_zero {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {r : ι → ℝ} (hr : Function.Injective r)
    (hnodal : Polynomial.aeval A (Lagrange.nodal Finset.univ r) = 0)
    {q : Polynomial ℝ} (hdeg : q.degree < Fintype.card ι) (hq : ∀ i, 0 ≤ q.eval (r i)) :
    (Polynomial.aeval A q).PosSemidef := by
  classical
  have hq' : q = Lagrange.interpolate Finset.univ r fun i => q.eval (r i) :=
    Lagrange.eq_interpolate hr.injOn (by rwa [Finset.card_univ])
  rw [hq', Lagrange.interpolate_apply, map_sum]
  refine Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add) Matrix.PosSemidef.zero
    fun i _ => ?_
  rw [map_mul, Polynomial.aeval_C, IsScalarTower.algebraMap_apply ℝ ℂ (Matrix n n ℂ),
    ← Algebra.smul_def]
  exact (posSemidef_aeval_lagrangeBasis hA hr hnodal i).smul
    (by simpa using RCLike.ofReal_nonneg (K := ℂ) |>.mpr (hq i))

end LatticeSystem.Math

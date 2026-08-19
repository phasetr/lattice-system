import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Matrix.Order

/-!
# Positive semidefiniteness from an annihilating polynomial with distinct real nodes

If a Hermitian matrix `A` satisfies a real-coefficient polynomial identity
`∏_i (X − r i) ` (`aeval A = 0`) at pairwise distinct real nodes `r i`, and a polynomial `q` of
degree `< card ι` is nonnegative at every node, then `aeval A q` is positive semidefinite.  The
route is Lagrange interpolation: `q = Σ_i q(r i) • basis i`, each Lagrange basis polynomial
`basis i` becomes a Hermitian idempotent under `aeval A` (so `aeval A (basis i) = Pᴴ P` for
`P = aeval A (basis i)` itself), and a nonnegative combination of positive-semidefinite matrices is
positive semidefinite.

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

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- **`aeval A` of a real polynomial is Hermitian when `A` is.**  Real coefficients are true *by
type* (`p : Polynomial ℝ`), so no `star`-of-polynomial hypothesis is needed. -/
private theorem isHermitian_aeval_real {A : Matrix n n ℂ} (hA : A.IsHermitian) (p : Polynomial ℝ) :
    (Polynomial.aeval A p).IsHermitian := by
  sorry -- dev-implement: `Polynomial.aeval_eq_sum_range` + `Matrix.IsHermitian.pow`/`.smul`.

/-- **A polynomial vanishing at every node of an injective family is divisible by the nodal
polynomial.**  `Lagrange.nodal Finset.univ r = ∏_i (X − C (r i))`; pairwise coprimality of the
factors (`Polynomial.pairwise_coprime_X_sub_C`) upgrades "vanishes at each root" to
"divisible by the product" (`Polynomial.dvd_iff_isRoot`, `Finset.prod_dvd_of_coprime`). -/
private theorem nodal_dvd_of_eval_eq_zero {r : ι → ℝ} (hr : Function.Injective r)
    {p : Polynomial ℝ} (hp : ∀ i, p.eval (r i) = 0) : Lagrange.nodal Finset.univ r ∣ p := by
  sorry -- dev-implement: `Finset.prod_dvd_of_coprime` + `Polynomial.pairwise_coprime_X_sub_C`
        -- + `Polynomial.dvd_iff_isRoot`.

/-- **The Lagrange basis polynomials become Hermitian idempotents under `aeval A`.**  If `A` is
Hermitian and annihilates the nodal polynomial of an injective node family, then for every index
`i` the matrix `aeval A (Lagrange.basis Finset.univ r i)` is positive semidefinite: `(basis i)² −
basis i` vanishes at every node, hence is divisible by the nodal polynomial, hence `aeval A` of it
is `0`, i.e. the image is Hermitian idempotent `P`, so `P = Pᴴ P` and
`Matrix.posSemidef_conjTranspose_mul_self` applies. -/
private theorem posSemidef_aeval_lagrangeBasis {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {r : ι → ℝ} (hr : Function.Injective r)
    (hnodal : Polynomial.aeval A (Lagrange.nodal Finset.univ r) = 0) (i : ι) :
    (Polynomial.aeval A (Lagrange.basis Finset.univ r i)).PosSemidef := by
  sorry -- dev-implement: `Lagrange.eval_basis_self`/`_of_ne` + `nodal_dvd_of_eval_eq_zero`
        -- + `Matrix.posSemidef_conjTranspose_mul_self`.

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
  sorry -- dev-implement: `Lagrange.eq_interpolate_of_eval_eq` + `Lagrange.interpolate_apply`
        -- + `posSemidef_aeval_lagrangeBasis` + `Matrix.PosSemidef.add`/`.zero`/`.smul`.

end LatticeSystem.Math

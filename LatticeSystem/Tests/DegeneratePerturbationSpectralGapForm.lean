import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation

/-!
# Test coverage for the Lemma 10.1 gap quadratic forms (Tasaki §10.1)

Pins the API contract of the three spectral-gap declarations that the Lemma 10.1 development
builds on top of the `DegeneratePerturbation.lean` definitions (`matrixKernel`,
`kernelProjectionMatrix`, `IsReducedInverse`, `secondOrderEffectiveHamiltonian`,
`IsUniqueGroundStateOn`):

1. `matrixKernel_orthogonal_gap` — the spectral-gap quadratic form for `H0` on
   `(ker H0)ᗮ`: `∃ g > 0, ∀ u ∈ (ker H0)ᗮ, g‖u‖² ≤ re⟪u, H0 u⟫`.
2. `IsUniqueGroundStateOn.orthogonal_gap` — the analogous gap for a Hermitian `H` with a
   unique ground state `φ` on an `H`-invariant `K`, restricted to `K ⊓ (ℂ∙φ)ᗮ`:
   `∃ δ > 0, ∀ w ∈ K ⊓ (ℂ∙φ)ᗮ, (E+δ)‖w‖² ≤ re⟪w, Hw⟫`.
3. `IsReducedInverse.norm_toEuclideanLin_le` — the corollary bounding the reduced inverse's
   operator norm by the reciprocal gap: `‖H0inv u‖ ≤ ‖u‖ / g`.

The quadratic-form shape (`c * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ x (Matrix.toEuclideanLin H x))`)
follows the `isSymmetric_block_lower` precedent in
`LatticeSystem/Math/MatrixAnalysis/CourantFischer.lean`.
-/

namespace LatticeSystem.Tests.DegeneratePerturbationSpectralGapForm

open LatticeSystem.Math Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pins the gap quadratic form for `H0` restricted to `(ker H0)ᗮ`: a *strictly positive*,
hypothesis-free gap `g` (no side condition, so the degenerate corners `ker H0 = ⊤` and
`dim ker H0 = 1` are covered by the same statement, the `∀ u ∈ (ker H0)ᗮ` clause being vacuous
when `(ker H0)ᗮ = ⊥`). -/
example {H0 : Matrix n n ℂ} (hH0pos : H0.PosSemidef) :
    ∃ g : ℝ, 0 < g ∧ ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)) :=
  matrixKernel_orthogonal_gap hH0pos

/-- Pins the gap quadratic form for a Hermitian `H` with a unique ground state `φ` on `K`,
restricted to the orthogonal complement of `φ` inside `K`. The degenerate corner
`dim ker H0 = 1` (hence `K` one-dimensional) makes the `∀ w ∈ K ⊓ (span {φ})ᗮ` clause vacuous,
so `δ > 0` must still be produced unconditionally, exactly as for `matrixKernel_orthogonal_gap`.

`H`-invariance of `K` is not decorative: without it the energy minimiser on `K` need not be an
eigenvector of `H`, and the bound is false. Witness: `H = diag(0, 10, -10)`,
`K = span {e₀, e₁ + e₂}`, `φ = e₀`, `E = 0` — the only eigenvectors of `H` inside `K` are the
multiples of `e₀`, so `φ` is the unique ground state on `K`, yet
`re⟪e₁ + e₂, H (e₁ + e₂)⟫ = 0` while `‖e₁ + e₂‖² = 2`, forcing `δ ≤ 0`. -/
example {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ} {E : ℝ}
    {φ : EuclideanSpace ℂ n} (hH : H.IsHermitian)
    (hKinv : ∀ v ∈ K, Matrix.toEuclideanLin H v ∈ K)
    (hGS : IsUniqueGroundStateOn K H E φ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : EuclideanSpace ℂ n, w ∈ K ⊓ (Submodule.span ℂ {φ})ᗮ →
      (E + δ) * ‖w‖ ^ 2 ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin H w)) :=
  IsUniqueGroundStateOn.orthogonal_gap hH hKinv hGS

/-- Pins the corollary `‖H0inv u‖ ≤ ‖u‖/g`, derived from `P₀ H0inv = 0` (so the reduced inverse
lands in `(ker H0)ᗮ`) composed with the coercivity bound there. -/
example {H0 H0inv : Matrix n n ℂ} (hInv : IsReducedInverse H0 H0inv) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (u : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin H0inv u‖ ≤ ‖u‖ / g :=
  hInv.norm_toEuclideanLin_le hg hgap u

end LatticeSystem.Tests.DegeneratePerturbationSpectralGapForm

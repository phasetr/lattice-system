import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation

/-!
# Test coverage for the Lemma 10.1 PR-1 gap quadratic forms (Tasaki §10.1, Step A)

**RED (TDD).** Pins the API contract of the three "Step A" declarations that PR-1
(`.self-local/reports/design-lemma-10-1-discharge-feasibility.md` §3 Step A, §6 PR-1 row)
adds to `LatticeSystem.Math` alongside the existing `DegeneratePerturbation.lean`
definitions (`matrixKernel`, `kernelProjectionMatrix`, `IsReducedInverse`,
`secondOrderEffectiveHamiltonian`, `IsUniqueGroundStateOn`). None of the three
target names exist yet, so this module is expected to fail to build until PR-1's
implementation lands:

1. `matrixKernel_orthogonal_gap` — the spectral-gap quadratic form for `H0` on
   `(ker H0)ᗮ`: `∃ g > 0, ∀ u ∈ (ker H0)ᗮ, g‖u‖² ≤ re⟪u, H0 u⟫`.
2. `IsUniqueGroundStateOn.orthogonal_gap` — the analogous gap for a Hermitian `H` with a
   unique ground state `φ` on `K`, restricted to `K ⊓ (ℂ∙φ)ᗮ`:
   `∃ δ > 0, ∀ w ∈ K ⊓ (ℂ∙φ)ᗮ, (E+δ)‖w‖² ≤ re⟪w, Hw⟫`.
3. `IsReducedInverse.norm_toEuclideanLin_le` — the Step A corollary bounding the reduced
   inverse's operator norm by the reciprocal gap: `‖H0inv u‖ ≤ ‖u‖ / g`.

The quadratic-form shape (`c * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ x (Matrix.toEuclideanLin H x))`)
follows the existing `isSymmetric_block_lower` precedent in
`LatticeSystem/Math/MatrixAnalysis/CourantFischer.lean:83-93`, which is the generic tool
Step A is expected to specialise (restrict to the eigenbasis support outside the kernel /
outside `Φeff`).

Every `example` below is a **signature shim** (Method D,
`docs/refactoring-conventions.md` §1): the statement type-checks against only the
already-existing `LatticeSystem.Math` API, but the body names a not-yet-defined
declaration, so `lake build LatticeSystem.Tests` must fail at these three names until
PR-1 supplies them. No production logic is introduced by this file.
-/

namespace LatticeSystem.Tests.DegeneratePerturbationSpectralGapForm

open LatticeSystem.Math Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **RED**: `matrixKernel_orthogonal_gap` does not exist yet.
Pins the Step A gap quadratic form for `H0` restricted to `(ker H0)ᗮ`
(design report §3 Step A, first bullet): a *strictly positive*, hypothesis-free gap
`g` (no side condition, so the degenerate corners P4a `ker H0 = ⊤` and P4b
`dim ker H0 = 1` of the design report's §5 pitfall P4 are covered by the same
statement, the `∀ u ∈ (ker H0)ᗮ` clause being vacuous when `(ker H0)ᗮ = ⊥`). -/
example {H0 : Matrix n n ℂ} (hH0pos : H0.PosSemidef) :
    ∃ g : ℝ, 0 < g ∧ ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)) :=
  matrixKernel_orthogonal_gap hH0pos

/-- **RED**: `IsUniqueGroundStateOn.orthogonal_gap` does not exist yet.
Pins the Step A gap quadratic form for a Hermitian `H` with a unique ground state `φ`
on `K` (design report §3 Step A, second bullet), restricted to the orthogonal
complement of `φ` inside `K`. The degenerate corner P4b (`dim ker H0 = 1`, hence
`K` one-dimensional) makes the `∀ w ∈ K ⊓ (span {φ})ᗮ` clause vacuous, so `δ > 0`
must still be produced unconditionally, exactly as for `matrixKernel_orthogonal_gap`. -/
example {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ} {E : ℝ}
    {φ : EuclideanSpace ℂ n} (hH : H.IsHermitian) (hGS : IsUniqueGroundStateOn K H E φ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : EuclideanSpace ℂ n, w ∈ K ⊓ (Submodule.span ℂ {φ})ᗮ →
      (E + δ) * ‖w‖ ^ 2 ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin H w)) :=
  IsUniqueGroundStateOn.orthogonal_gap hH hGS

/-- **RED**: `IsReducedInverse.norm_toEuclideanLin_le` does not exist yet.
Pins the Step A corollary of the design report §3 (`‖H0inv u‖ ≤ ‖u‖/g`, derived from
`P₀ H0inv = 0 ⇒ range H0inv ⊆ H⊥` composed with the `matrixKernel_orthogonal_gap`
coercivity bound). -/
example {H0 H0inv : Matrix n n ℂ} (hInv : IsReducedInverse H0 H0inv) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (u : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin H0inv u‖ ≤ ‖u‖ / g :=
  hInv.norm_toEuclideanLin_le hg hgap u

end LatticeSystem.Tests.DegeneratePerturbationSpectralGapForm

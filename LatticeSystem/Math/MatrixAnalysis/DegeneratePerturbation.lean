import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.Order.Field

/-!
# Degenerate perturbation theory: the second-order effective Hamiltonian (Tasaki Lemma 10.1)

This file formalizes **Tasaki Lemma 10.1** (Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.1,
eq. (10.1.20), p. 346): the degenerate-perturbation-theory statement that
underlies the proof of Lieb's theorem for the repulsive Hubbard model
(§10.2.2).

For a Hamiltonian family `Ĥ(λ) = Ĥ₀ + λ V̂` with `Ĥ₀ ≥ 0` Hermitian and
ground space `H₀ = ker Ĥ₀`, the second-order effective Hamiltonian on `H₀`
is

  `Ĥeff = − P̂₀ V̂ Ĥ₀⁻¹ V̂ P̂₀`,   (eq. (10.1.20))

where `P̂₀` is the orthogonal projection onto `H₀` and `Ĥ₀⁻¹` is the reduced
(Moore–Penrose) inverse, supported on `H₀ᗮ`. The second-order formula
applies when the first-order term vanishes on the degenerate subspace,
`P̂₀ V̂ P̂₀ = 0` (so that Tasaki's `Ĥspin = λ² Ĥeff`, eq. (10.1.6), has no
`λ¹` contribution). Lemma 10.1 states: if `Ĥeff` (restricted to `H₀`) has
a unique ground state `|Φeff-GS⟩`, then `Ĥ(λ)` has a unique ground state for
all sufficiently small `λ > 0`, and a phase choice of normalized ground
states converges to `|Φeff-GS⟩` as `λ → 0⁺`.

## Status

The content of Lemma 10.1 is the analytic theory of degenerate
perturbations: continuity of the low-lying eigenstates and the `λ → 0⁺`
limit. Per the project policy (perturbation-theory proofs are not
undertaken; deep analytic results are faithful documented axioms), the
lemma is recorded as a documented `axiom`
(`tasaki_lemma_10_1_degenerate_perturbation`), in the same spirit as the
strong-coupling companion `effectiveHamiltonian_strongCoupling_limit`
(Theorem A.12, `Math/EffectiveLimit.lean`). The supporting projection
matrix is constructed concretely, and its Hermitian/idempotent properties
are proved as consistency guards.
-/

namespace LatticeSystem.Math

open Matrix Filter Topology
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The kernel of a finite matrix, as a subspace of `EuclideanSpace ℂ n`
via `Matrix.toEuclideanLin`. -/
noncomputable def matrixKernel (H : Matrix n n ℂ) :
    Submodule ℂ (EuclideanSpace ℂ n) :=
  LinearMap.ker (Matrix.toEuclideanLin H)

/-- The orthogonal projection matrix `P̂₀` onto `ker H`, expressed in the
standard orthonormal basis of `EuclideanSpace ℂ n`. -/
noncomputable def kernelProjectionMatrix (H : Matrix n n ℂ) : Matrix n n ℂ :=
  LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun n ℂ)
    (matrixKernel H).starProjection.toLinearMap

/-- The matrix element of `P̂₀` is the inner product
`(P̂₀)_{xy} = ⟪e_x, P̂₀ e_y⟫`. -/
theorem kernelProjectionMatrix_apply (H : Matrix n n ℂ) (x y : n) :
    kernelProjectionMatrix H x y
      = inner ℂ (EuclideanSpace.basisFun n ℂ x)
        ((matrixKernel H).starProjection (EuclideanSpace.basisFun n ℂ y)) := by
  rw [kernelProjectionMatrix, LinearMap.toMatrixOrthonormal_apply_apply]
  rfl

/-- **`P̂₀` is Hermitian** (the orthonormal-basis matrix of a self-adjoint
projection). -/
theorem kernelProjectionMatrix_isHermitian (H : Matrix n n ℂ) :
    (kernelProjectionMatrix H).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply, kernelProjectionMatrix_apply,
    kernelProjectionMatrix_apply, ← starRingEnd_apply, inner_conj_symm]
  exact Submodule.inner_starProjection_left_eq_right (matrixKernel H) _ _

/-- **`P̂₀` is idempotent**: `P̂₀ · P̂₀ = P̂₀`. -/
theorem kernelProjectionMatrix_isIdempotent (H : Matrix n n ℂ) :
    kernelProjectionMatrix H * kernelProjectionMatrix H = kernelProjectionMatrix H := by
  have h := (matrixKernel H).isIdempotentElem_starProjection
  unfold kernelProjectionMatrix
  rw [← map_mul (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun n ℂ))]
  congr 1
  rw [← ContinuousLinearMap.coe_mul, h]

/-- `H0inv` is the **reduced (Moore–Penrose) inverse** of `H0`: it inverts
`H0` on `(ker H0)ᗮ` and vanishes on `ker H0`. We axiomatize this property
(mathlib has no general pseudo-inverse construction) and pass `H0inv` as
data to the effective-Hamiltonian definition. -/
structure IsReducedInverse (H0 H0inv : Matrix n n ℂ) : Prop where
  /-- `H0 · H0inv = 1 − P̂₀` (inverts `H0` on the orthogonal complement of `ker H0`). -/
  left_inv_on_compl : H0 * H0inv = 1 - kernelProjectionMatrix H0
  /-- `H0inv · H0 = 1 − P̂₀`. -/
  right_inv_on_compl : H0inv * H0 = 1 - kernelProjectionMatrix H0
  /-- `H0inv` annihilates `ker H0` from the left. -/
  kills_kernel_left : kernelProjectionMatrix H0 * H0inv = 0
  /-- `H0inv` annihilates `ker H0` from the right. -/
  kills_kernel_right : H0inv * kernelProjectionMatrix H0 = 0
  /-- `H0inv` is Hermitian. -/
  hermitian : H0inv.IsHermitian

/-- The **second-order effective Hamiltonian** `Ĥeff = − P̂₀ V̂ Ĥ₀⁻¹ V̂ P̂₀`
(Tasaki eq. (10.1.20)). -/
noncomputable def secondOrderEffectiveHamiltonian (H0 V H0inv : Matrix n n ℂ) :
    Matrix n n ℂ :=
  -(kernelProjectionMatrix H0 * V * H0inv * V * kernelProjectionMatrix H0)

/-- The **perturbed Hamiltonian** `Ĥ(λ) = Ĥ₀ + λ V̂`. -/
noncomputable def perturbedHamiltonian (H0 V : Matrix n n ℂ) (lam : ℝ) :
    Matrix n n ℂ :=
  H0 + (lam : ℂ) • V

/-- `E` is the **ground (lowest) eigenvalue** of `H`, restricted to a
subspace `K`: some nonzero `φ ∈ K` is an `E`-eigenvector, and every
eigenvalue with an eigenvector in `K` is `≥ E`. -/
def IsGroundEigenvalueOn (K : Submodule ℂ (EuclideanSpace ℂ n))
    (H : Matrix n n ℂ) (E : ℝ) : Prop :=
  (∃ φ : EuclideanSpace ℂ n,
      φ ∈ K ∧ φ ≠ 0 ∧ Matrix.toEuclideanLin H φ = (E : ℂ) • φ) ∧
    ∀ μ : ℝ, (∃ ψ : EuclideanSpace ℂ n,
        ψ ∈ K ∧ ψ ≠ 0 ∧ Matrix.toEuclideanLin H ψ = (μ : ℂ) • ψ) → E ≤ μ

/-- `φ` is the **unique normalized ground state** of `H` on `K`: it is a
normalized `E`-eigenvector in `K`, `E` is the ground eigenvalue on `K`, and
every `E`-eigenvector in `K` is a scalar multiple of `φ`. -/
def IsUniqueGroundStateOn (K : Submodule ℂ (EuclideanSpace ℂ n))
    (H : Matrix n n ℂ) (E : ℝ) (φ : EuclideanSpace ℂ n) : Prop :=
  φ ∈ K ∧ ‖φ‖ = 1 ∧ Matrix.toEuclideanLin H φ = (E : ℂ) • φ ∧
    IsGroundEigenvalueOn K H E ∧
    ∀ ψ : EuclideanSpace ℂ n, ψ ∈ K →
      Matrix.toEuclideanLin H ψ = (E : ℂ) • ψ → ∃ c : ℂ, ψ = c • φ

/-- **Tasaki Lemma 10.1 (degenerate perturbation theory), AXIOM.**
(1st ed., Springer 2020, §10.1, Lemma 10.1 / eq. (10.1.20), p. 346.)

For `Ĥ(λ) = Ĥ₀ + λ V̂` with `Ĥ₀ ≥ 0` Hermitian, `V̂` Hermitian, `H0inv`
a reduced inverse of `Ĥ₀`, and the **first-order term vanishing on the
degenerate subspace** (`P̂₀ V̂ P̂₀ = 0`, the condition under which the
effective theory is governed by the second-order term — Tasaki eq.
(10.1.6), `Ĥspin = λ² Ĥeff`, has no `λ¹` term): if the second-order
effective Hamiltonian `Ĥeff = − P̂₀ V̂ Ĥ₀⁻¹ V̂ P̂₀` has a unique ground
state `Φeff` on the kernel `H₀ = ker Ĥ₀`, then there is `λ₀ > 0` such that
for every `λ ∈ (0, λ₀)` the
perturbed Hamiltonian `Ĥ(λ)` has a unique ground state on the whole space,
and (a phase choice of) these normalized ground states converges to `Φeff`
as `λ → 0⁺`.

This is the analytic theory of degenerate perturbations (continuity of the
low-lying eigenstates and the `λ → 0⁺` limit); recorded as a faithful
documented axiom per the project policy. -/
axiom tasaki_lemma_10_1_degenerate_perturbation [Nonempty n]
    (H0 V H0inv : Matrix n n ℂ)
    (hH0 : H0.IsHermitian) (hH0pos : H0.PosSemidef) (hV : V.IsHermitian)
    (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (Eeff : ℝ) (Φeff : EuclideanSpace ℂ n)
    (hEffGS : IsUniqueGroundStateOn (matrixKernel H0)
      (secondOrderEffectiveHamiltonian H0 V H0inv) Eeff Φeff) :
    ∃ lam0 : ℝ, 0 < lam0 ∧
      ∃ Elam : ℝ → ℝ, ∃ Philam : ℝ → EuclideanSpace ℂ n,
        (∀ lam : ℝ, 0 < lam → lam < lam0 →
          IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
            (perturbedHamiltonian H0 V lam) (Elam lam) (Philam lam)) ∧
        Tendsto Philam (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 Φeff)

end LatticeSystem.Math

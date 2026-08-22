import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation

/-!
# Shared scaffolding for the explicit witnesses of the Lemma 10.1 test files

The test files of the Tasaki Lemma 10.1 arc (`Tests/DegeneratePerturbationFeshbach.lean`,
`Tests/DegeneratePerturbationGroundEnergy.lean`, `Tests/DegeneratePerturbationUniqueness.lean`)
instantiate their API pins on explicit matrices over `Fin 1`, `Fin 2` and `Fin 4`. This module
holds the facts more than one of them needs, so that no declaration is duplicated across them:

* `toEuclideanLin_apply_coord` — the coordinate readout of a matrix action, the entry point of
  every explicit finite-dimensional computation in those files;
* `fin1_matrixKernel_zero_eq_top` / `fin1_kernelProjectionMatrix_zero_eq_one` — the `Ĥ₀ = 0`
  degeneration on `Fin 1`, where `ker Ĥ₀` is the whole space and the kernel projection is the
  identity matrix. It carries the `V = 0` corner of the trial-state bound and the two
  load-bearing counterexamples of the Feshbach equivalence.
-/

namespace LatticeSystem.Tests.DegeneratePerturbationWitness

open LatticeSystem.Math Matrix

/-- Coordinates of a matrix acting on `EuclideanSpace ℂ n`: the action is `mulVec`, so the `i`-th
coordinate pairs the `i`-th row with the vector. -/
theorem toEuclideanLin_apply_coord {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (x : EuclideanSpace ℂ n) (i : n) :
    (Matrix.toEuclideanLin M x) i = ∑ j, M i j * x j := rfl

/-- The kernel of the zero matrix is the whole space. -/
theorem fin1_matrixKernel_zero_eq_top :
    matrixKernel (0 : Matrix (Fin 1) (Fin 1) ℂ) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  simp [matrixKernel]

/-- With `ker Ĥ₀ = ⊤` the kernel projection `P̂₀` is the identity matrix, because the star
projection onto `⊤` is the identity map. -/
theorem fin1_kernelProjectionMatrix_zero_eq_one :
    kernelProjectionMatrix (0 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  refine Matrix.toEuclideanLin.injective ?_
  rw [toEuclideanLin_kernelProjectionMatrix, fin1_matrixKernel_zero_eq_top,
    Submodule.starProjection_top]
  ext x
  simp

end LatticeSystem.Tests.DegeneratePerturbationWitness

import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueLipschitz
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueContinuous

/-!
# Minimum energy of a Hamiltonian restricted to a subspace (Tasaki Theorem 10.4)

This file formalizes the **minimum energy on a subspace** ingredient of Tasaki Theorem 10.4
(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 351): for a Hamiltonian `H` and a candidate low-energy subspace `W`, the quantity

  `minEnergyOn W H = inf { re ⟪v, H v⟫ | v ∈ W, ‖v‖ = 1 }`

is the lowest value the energy functional attains on the unit sphere of `W`. Theorem 10.4 compares
`minEnergyOn` on two competing subspaces (the trial ferromagnetic sector and its complement) to
pin down the ground-state sector of the attractive Hubbard model.

This is a **thin wrapper** around existing infrastructure:

* reachability is `exists_unit_eigenvector_min_energy_on_invariant`
  (`DegeneratePerturbation.lean`), repackaged as an `IsGroundEigenvalueOn` witness;
* the entry-norm Lipschitz bound and the parameter-continuity corollary mirror
  `abs_hermitianMinEigenvalue_sub_le_sum_entryNorms` and `Continuous.hermitianMinEigenvalue_comp`
  (`HermitianMinEigenvalueLipschitz.lean` / `HermitianMinEigenvalueContinuous.lean`), specialized
  from the whole space to unit vectors of a fixed nonzero subspace `W`.

Unlike `hermitianMinEigenvalue`, `minEnergyOn` does not require `H` to be Hermitian to be
*defined*: only the real part of the (possibly non-Hermitian) Rayleigh quotient is taken. The
Hermitian hypothesis is only needed for the reachability statement, where it guarantees an
eigenvector witness.
-/

namespace LatticeSystem.Math

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **minimum energy** of `H` on the subspace `W`: the infimum, over unit vectors `v ∈ W`, of
the real part of the Rayleigh quotient `⟪v, H v⟫` (Tasaki §10.2.3, p. 351). -/
noncomputable def minEnergyOn (W : Submodule ℂ (EuclideanSpace ℂ n)) (H : Matrix n n ℂ) : ℝ :=
  sInf {r : ℝ | ∃ v ∈ W, ‖v‖ = 1 ∧ r = RCLike.re (inner ℂ v (Matrix.toEuclideanLin H v))}

/-- **Reachability**: if `H` is Hermitian and preserves the nonzero subspace `W`, then
`minEnergyOn W H` is the ground eigenvalue of `H` on `W`, attained by a unit eigenvector of `H`
lying in `W`. This repackages `exists_unit_eigenvector_min_energy_on_invariant` as an
`IsGroundEigenvalueOn` witness. -/
theorem minEnergyOn_isGroundEigenvalueOn {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {W : Submodule ℂ (EuclideanSpace ℂ n)}
    (hInv : ∀ v ∈ W, Matrix.toEuclideanLin H v ∈ W) (hW : W ≠ ⊥) :
    IsGroundEigenvalueOn W H (minEnergyOn W H) := by
  sorry

/-- **Entry-norm Lipschitz continuity** of `minEnergyOn W` in the matrix argument: bounded by the
sum of entrywise norm differences, uniformly over the choice of nonzero subspace `W`. Mirrors
`abs_hermitianMinEigenvalue_sub_le_sum_entryNorms`, restricted to unit vectors of `W` rather than
the whole space. -/
theorem abs_minEnergyOn_sub_le_sum_entryNorms {W : Submodule ℂ (EuclideanSpace ℂ n)}
    (hW : W ≠ ⊥) (H₁ H₂ : Matrix n n ℂ) :
    |minEnergyOn W H₁ - minEnergyOn W H₂| ≤ ∑ i, ∑ j, ‖(H₁ - H₂) i j‖ := by
  sorry

/-- **Continuity of `minEnergyOn W` under a continuous matrix-valued parameter**: if
`F : X → Matrix n n ℂ` is continuous, so is `x ↦ minEnergyOn W (F x)`. Mirrors
`Continuous.hermitianMinEigenvalue_comp`, via the Lipschitz bound
`abs_minEnergyOn_sub_le_sum_entryNorms` in place of the Hermitian-specific one. -/
theorem Continuous.minEnergyOn_comp {W : Submodule ℂ (EuclideanSpace ℂ n)} (hW : W ≠ ⊥)
    {X : Type*} [PseudoMetricSpace X] {F : X → Matrix n n ℂ} (hF : Continuous F) :
    Continuous (fun x => minEnergyOn W (F x)) := by
  sorry

end LatticeSystem.Math

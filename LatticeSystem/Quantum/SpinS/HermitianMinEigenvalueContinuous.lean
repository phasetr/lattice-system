import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueLipschitz
import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of `hermitianMinEigenvalue` composed with a continuous Hermitian-valued function

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

For a topological space `X` and a continuous matrix-valued function
`F : X → Matrix n n ℂ` such that `F x` is Hermitian for every `x`, the function
`x ↦ hermitianMinEigenvalue (hHerm x)` is continuous on `X`.

Proof: by the Lipschitz bound (PR #3952),
`|hermitianMinEigenvalue hA - hermitianMinEigenvalue hB| ≤ Σ ‖(A-B)_{ij}‖`.
The RHS is continuous in (A, B) and vanishes at A = B, giving continuity of the
LHS via Lipschitz → continuous.

This is the immediate consequence of PR #3952 that produces continuity of the
per-sector min eigenvalue in `(λ, D)` for the obligation (2) deformation argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {X : Type*} [PseudoMetricSpace X]

/-- Entry-norm sum is continuous in the matrix parameter. -/
theorem continuous_sum_entryNorms :
    Continuous (fun M : Matrix n n ℂ => ∑ i, ∑ j, ‖M i j‖) := by
  refine continuous_finset_sum _ (fun i _ => ?_)
  refine continuous_finset_sum _ (fun j _ => ?_)
  exact (continuous_apply_apply i j).norm

/-- **Continuity of `hermitianMinEigenvalue` composed with a continuous Hermitian
matrix-valued function**. Given continuous `F : X → Matrix n n ℂ` such that each
`F x` is Hermitian, the function `x ↦ hermitianMinEigenvalue (hHerm x)` is
continuous. -/
theorem Continuous.hermitianMinEigenvalue_comp
    {F : X → Matrix n n ℂ} (hF : Continuous F)
    (hHerm : ∀ x, (F x).IsHermitian) :
    Continuous (fun x => hermitianMinEigenvalue (hHerm x)) := by
  refine Metric.continuous_iff.mpr (fun x₀ ε hε => ?_)
  -- By continuity of entry-norm sum at F x₀ - F x₀ = 0, choose δ.
  have hcont : ContinuousAt (fun x => ∑ i, ∑ j, ‖(F x - F x₀) i j‖) x₀ := by
    have hcontF : Continuous (fun x => F x - F x₀) :=
      hF.sub (continuous_const : Continuous (fun _ : X => F x₀))
    exact continuous_sum_entryNorms.continuousAt.comp hcontF.continuousAt
  -- ∑ ‖(F x₀ - F x₀)_ij‖ = 0 at x = x₀.
  have hzero : (∑ i, ∑ j, ‖(F x₀ - F x₀) i j‖) = 0 := by
    simp
  -- For ε > 0, find δ s.t. |x - x₀| < δ → ∑ ‖(F x - F x₀)_ij‖ < ε.
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont ε hε
  refine ⟨δ, hδ_pos, fun x hx => ?_⟩
  have hsumlt : ∑ i, ∑ j, ‖(F x - F x₀) i j‖ < ε := by
    have := hδ hx
    rw [hzero, Real.dist_eq, sub_zero] at this
    have hsumnn : (0 : ℝ) ≤ ∑ i, ∑ j, ‖(F x - F x₀) i j‖ := by
      refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
    rw [abs_of_nonneg hsumnn] at this
    exact this
  -- Apply Lipschitz: |min A - min B| ≤ Σ ‖(A - B)_ij‖.
  have hlip := abs_hermitianMinEigenvalue_sub_le_sum_entryNorms (hHerm x) (hHerm x₀)
  -- dist (min(F x)) (min(F x₀)) = |min(F x) - min(F x₀)| ≤ Σ ‖(F x - F x₀)_ij‖ < ε.
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hlip hsumlt

end LatticeSystem.Quantum
